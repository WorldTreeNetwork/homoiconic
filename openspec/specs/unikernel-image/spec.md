# unikernel-image

What is built: one program runs in a Cloud Hypervisor machine with no operating system in it. `unikernel/out/reflect.elf` is a static x86_64 ELF file started by direct kernel boot. It holds the boot code (`unikernel/boot.S`), a Zig layer that stands where an operating system would (`unikernel/kernel.zig`, `unikernel/main.zig`), Zig's musl, the Lean runtime, and the same compiled Lean objects as its Linux comparison process, `unikernel/out/reflect-linux`. The program and its step budget are built into the image; on boot it calls `reflect_run`, writes the answer to the serial port and powers off. Given a program's byte form at boot with Cloud Hypervisor's `--initramfs`, the layer moves those bytes above the image, serves them as the read-only file `/boot/program`, and the image runs them through `reflect_interp` instead, with the step budget and interpreter levels taken from the PVH command line, so one image file runs any number of programs, one per boot (`openspec/changes/archive/2026-11-22-add-boot-program-bytes/`). `unikernel/out/reply source <file>` writes a source's byte form. `unikernel/build.sh` builds it and `unikernel/check.sh` boots it and checks it. Nothing in this capability is proved; it is trusted as the host is (`docs/PROOFS.md`).

## Purpose

State what the image does, what it leaves to Lean, what it refuses or reports instead of providing, and what its build and check must show. This spec does not cover a network device (that is `openspec/specs/unikernel-net/spec.md`), source text given at boot, more than one boot module, more than one thread, aarch64, or building on macOS.

## Requirements

### Requirement: One image boots under Cloud Hypervisor with no operating system

The build SHALL produce one static x86_64 ELF file that Cloud Hypervisor starts by direct kernel boot through the PVH entry, with no firmware, no file system and no operating system in the guest. Bytes handed to the image at boot with `--initramfs` are one program's byte form, not a file system. The image SHALL hold the same compiled Lean objects as its Linux comparison process. Lean SHALL own reading, compilation, evaluation and rendering. Non-Lean image code SHALL NOT implement a language reader or evaluator.

#### Scenario: The factorial program

- GIVEN an image built from `examples/factorial.hom`
- WHEN Cloud Hypervisor boots it with one processor and 512 MiB
- THEN the serial port shows `265252859812191058636308480000000`, the machine powers off, and Cloud Hypervisor exits with status 0

### Requirement: The image runs its program through the kernel and writes the kernel's text

On boot an image given no bytes SHALL pass the program source built into it, and the step budget built into it, to `reflect_run`; an image given bytes SHALL run them as the requirement "One image runs a byte form given at boot" says. In both cases it SHALL write the text that comes back to the serial port followed by a line end, and SHALL power the machine off. A syntax error, an error outcome, a run that does not finish in its budget, and a value are all text the kernel wrote, and all of them SHALL end with `reflect: exit 0`.

#### Scenario: A program that does not finish

- GIVEN an image built from `examples/forever.hom` with a budget of 5000
- WHEN it boots
- THEN the serial port shows `no result within 5000 steps` and then `reflect: exit 0`

#### Scenario: A program that is not syntax

- GIVEN an image built from a file the reader refuses
- WHEN it boots
- THEN the serial port shows the reader's error text, the same text `unikernel/out/reflect-linux` prints for that file, and then `reflect: exit 0`

### Requirement: What the image does not provide is said, not hidden

A system call the layer does not answer SHALL write a line naming its number to the serial port and SHALL return "not implemented". A processor fault SHALL write a line with the fault's number, the instruction's address and the faulting address, and SHALL power the machine off. Contiguous stack growth touching the unmapped, allocator-excluded 2 MiB guard below the 16 MiB stack SHALL fault on a separate fault stack before writing through the guard. Frames that skip the whole guard are outside this guarantee. The check SHALL fail when either line appears where it is not expected.

#### Scenario: A system call nobody answers

- GIVEN an image whose layer lacks an answer for a call the start-up makes
- WHEN the check boots it
- THEN the check fails and shows the line that names the call

#### Scenario: Nesting too deep

- GIVEN an image built from a program whose source nests deeper than the stack holds
- WHEN it boots
- THEN the serial port shows a processor page-fault report from the alternate fault stack, and the machine powers off

### Requirement: The image has one thread and no clock

The image SHALL run on one processor with one thread. It SHALL NOT start the Lean runtime's event loop. The time it reports SHALL NOT be relied on by anything a program computes. Random bytes SHALL come from the processor's random instruction, and an image on a processor without one SHALL say so and stop. Each result SHALL require the success carry flag, with at most ten attempts before a diagnostic and termination; no fallback is permitted.

### Requirement: Successful reproducible Linux build

The build SHALL compile the pinned Lean-generated C on Linux x86_64 and link the same objects into the image and Linux comparison process. Missing, modified, stale or wrong-platform artifacts SHALL fail validation. A clean output build SHALL succeed with Lean 4.35.0, Zig 0.16.0/musl 1.2.5 and Cloud Hypervisor 54.0 without requiring host/check.sh.

#### Scenario: Clean provenance

- GIVEN no unikernel output directory
- WHEN the check builds and boots factorial
- THEN it records toolchain versions, source provenance and object hashes, compares the complete serial stream to the Linux process and rejects changed inputs or objects on reuse

#### Scenario: Lean owns semantics

- GIVEN the image sources and linked objects
- WHEN their call paths and symbol references are inspected
- THEN non-Lean code only initializes, passes bytes and supplies runtime services; main calls reflect_run and reflect_interp and no other export that evaluates or reads, and the identical Lean objects occur in both links

### Requirement: Complete output and infrastructure errors

The image SHALL honor reflect_run's pointer/length/capacity contract, allocating the returned length and retrying when necessary. Initialization, allocation or write failures SHALL terminate unsuccessfully, distinct from a kernel outcome.

#### Scenario: Large rendering and zero bytes

- GIVEN an array whose rendering exceeds 65536 bytes, and separately a source containing a zero byte
- WHEN each image boots
- THEN its entire output matches the Linux process byte for byte, including newline and exit 0; the array also matches an independently generated expected rendering

### Requirement: Bounded syscall CPU state

The image SHALL reject CPUs without XSAVE before entering musl. It SHALL enable only x87/SSE and optional AVX, check CPUID's enabled save-area size against its 4096-byte reserve, align that area to 64 bytes and dispatch calls to 16 bytes. It SHALL preserve the red zone, flags, general registers except RAX/RCX/R11, and enabled floating/vector state across syscalls.

#### Scenario: Preservation

- GIVEN sentinel general registers, flags, 128 red-zone bytes and enabled floating/vector state
- WHEN a probe calls a handler that clobbers floating/vector state
- THEN all promised state survives; removing vector restore or red-zone protection makes the probe fail

#### Scenario: Feature rejection

- GIVEN a controlled build reporting XSAVE or RDRAND absent
- WHEN it boots
- THEN it prints the corresponding diagnostic and powers off before entering musl

#### Scenario: Guard integrity

- GIVEN a probe with a sentinel immediately below the guard
- WHEN it writes a named address inside the unmapped guard
- THEN fault 14 reports that address, confirms use of the alternate stack and the intact sentinel; successful write, reset and timeout fail the check

#### Scenario: Random failure and runtime isolation

- GIVEN controlled random exhaustion at startup or during a served request
- WHEN the image boots
- THEN it prints only the exhaustion diagnostic and powers off; positive probes serve getrandom and /dev/urandom through the same checked instruction path

#### Scenario: No event loop or semantic clock

- GIVEN the pinned source audit and image link
- WHEN initialization and reflect_run's path are inspected and factorial boots with time fixed at zero
- THEN initialize_libuv resolves to the empty image function, no thread creation is reached, and the factorial answer is unchanged

### Requirement: One image runs a byte form given at boot

When Cloud Hypervisor is started with `--initramfs <file>`, the image SHALL treat that file's bytes as one program's byte form (`wire-bytes`). It SHALL pass exactly those bytes to `reflect_interp` with the byte-form flag set and the text flag clear, SHALL write the text that comes back to the serial port followed by a line end, and SHALL power the machine off. The PVH command line SHALL be `[step-budget [levels [space]]]`: the budget SHALL default to the one built into the image, the levels to 1 and the space to the kernel's ("A run on the image has a space limit"); level 0 runs the program itself and level k runs it through k interpreters. The program built into the image SHALL NOT run when bytes are given. One image file SHALL serve any number of different byte forms, one per boot, without being built again.

The layer SHALL move the bytes out of the memory the stack and the allocators will use before it lays those out, SHALL NOT hand that memory out while the bytes are still read from it, and SHALL NOT read or change the bytes. Non-Lean code SHALL NOT decide whether the bytes are a program: bytes the kernel refuses SHALL end in the kernel's text and `reflect: exit 0`. More than 2 MiB of bytes, more than one boot module, or a boot module list that does not lie in usable memory, SHALL stop the image with a line saying so before the C library starts, and the layer SHALL check where the module list lies before it reads it. A PVH command line longer than 1023 bytes SHALL stop the image with a line saying so before the C library starts; the layer SHALL NOT cut it. Bytes that are no value SHALL be refused in the kernel's text however many arrays they open (`wire-bytes`). The limit is 2 MiB so that reading, lifting and printing any byte form within it fits the 512 MiB machine: at 4 MiB a literal array of empty texts, a literal array of empty arrays and a literal text of line ends each ran out of memory on morphie, and at 16 MiB one array of zeros did; at 2 MiB every shape measured ended in its answer or the kernel's text (`unikernel/README.md`, `homoiconic-q59.61`). Two costs are not bounded by it, and are stated as they are. A loop whose calls are in tail position SHALL run in constant memory: `examples/forever.hom`, 52 bytes, SHALL end in `no result within 100000000 steps` at the default budget at levels 0, 1 and 2 (`homoiconic-q59.65`; while a tail call kept a frame, levels 0 and 1 ran the machine out of memory). What a run keeps live still grows with its steps where the program keeps it, not with its bytes: a recursion whose calls wait on each other keeps a frame per pending call, and a program that builds data keeps the data. Such a run can exhaust the machine within the default budget, which ends in the Lean runtime's `INTERNAL PANIC: out of memory` and `reflect: exit 1`, not in the kernel's text: `def deep x = [x, ...deep x]`, 55 bytes, peaks at 15, 91, 259 and 849 MiB as a Linux process at 1M, 10M, 30M and 100M steps, and at the default budget the image ends in `INTERNAL PANIC: out of memory` (morphie, `unikernel/README.md`). The list of 209714 zeros written out as a 1 MiB program, which ran out of memory through one interpreter while a tail call kept a frame, now gives its answer at the default budget (317 MiB as a Linux process). No budget limit or depth limit prevents this (`homoiconic-q59.67`). A number near the limit is read and printed in time that grows with the square of its length and does not finish in practice (`homoiconic-q59.64`). A program whose answer is data nested deeper than the stack holds (from 262144 arrays deep on morphie) ends in the report of a full stack, as a deep source does. The network image's program bytes have their own, smaller bound: at most 1176 bytes, a frame of at most 1200 bytes less its 24-byte header, with a budget of at most 100000000 steps (`openspec/specs/unikernel-net/spec.md`).

The step budget SHALL be a whole number below 2^64 and the levels a whole number from 0 to 8. A budget or a level count that is not a whole number SHALL end in a line saying so and `reflect: exit 2`. A budget of 2^64 or more SHALL end in `reflect: the step budget must be below 18446744073709551616`, and more than 8 levels in `reflect: the levels must be at most 8`, each followed by `reflect: exit 2`, before the kernel is asked to run anything: the kernel builds the tower of interpreters before the budget counts a step. The bound is the kernel's, `Surface.maxLevels`, which the image asks for by the export `reflect_max_levels`; `main.zig` holds no number of its own (`openspec/specs/zig-host/spec.md`). The Linux comparison process SHALL take the same file and the same words, `reflect-linux <bytes-file> [step-budget [levels]]`, and call the same export.

Cloud Hypervisor 54.0 loads the ELF file and then copies the `--initramfs` file to the top of the first memory region without looking at where the ELF file lies, so a file nearly that large lands on the image before any of its code runs, and the image cannot refuse it. The documented launch, `unikernel/given.sh <bytes-file> [step-budget [levels]]`, SHALL refuse a file larger than 2 MiB with a line and status 2 before Cloud Hypervisor starts, and SHALL give the machine 512 MiB, so that a file it passes lies above the image. The check SHALL boot bytes through that launch.

#### Scenario: Two programs, one image

- GIVEN one image file, built once, and the byte forms of `examples/factorial.hom` and of a program whose answer is a text
- WHEN Cloud Hypervisor boots that file once with each byte form given at boot
- THEN each serial stream is byte for byte what the Linux process prints for the same bytes followed by `reflect: exit 0`, the factorial stream shows `265252859812191058636308480000000`, and the image file's hash is unchanged between the boots

#### Scenario: Levels and budget come from the command line

- GIVEN the factorial byte form and the byte form of `examples/forever.hom`
- WHEN the image boots with factorial and command lines naming 0, 1 and 2 levels, and with forever and the command line `5000`
- THEN factorial's answer is the same at every level, and forever shows `no result within 5000 steps`

#### Scenario: A tail loop at the default budget

- GIVEN the byte form of `examples/forever.hom`
- WHEN the image boots with it and the command lines `100000000 0`, `100000000 1` and `100000000 2`
- THEN each serial stream is what the Linux process prints, `no result within 100000000 steps`, followed by `reflect: exit 0` (`unikernel/check.sh`)

#### Scenario: The levels are not ignored

- GIVEN the factorial byte form
- WHEN the image boots with the command lines `10000 0`, `10000 1`, `100000 1` and `100000 2`
- THEN the first and third show factorial's answer, and the second and fourth `no result within` their budget, each as the Linux process shows it: ignoring the level would change at least one of them

#### Scenario: Words past the limits

- GIVEN the factorial byte form
- WHEN the image boots with the command lines `many`, `18446744073709551616`, `1000 x`, `1000 9` and `1000 4294967296`
- THEN each ends in its own line, as the Linux process ends: the budget is not a whole number, the budget must be below 2^64, the levels are not a whole number, and twice the levels must be at most 8, each followed by `reflect: exit 2`; and `1000 8` and `18446744073709551615 0` are run

#### Scenario: A long command line

- GIVEN a command line of 1023 bytes that names a budget of 5000, and one of 1101 bytes
- WHEN the image boots with each
- THEN the first runs with a budget of 5000, and the second shows only `reflect: the command line is longer than 1023 bytes`

#### Scenario: Bytes that are no program, and too many bytes

- GIVEN a megabyte of bytes that is no program, a program's byte form with one byte added, 2 MiB of zero bytes, 2 MiB of bytes that each open an array of one, a file of 2 MiB and one byte, and a file of 16 MiB
- WHEN the image boots with each
- THEN the first four end in the text the Linux process prints for them and `reflect: exit 0`: `bytes error: an indefinite length or a reserved form`, `bytes error: there are bytes after the value` twice, and `bytes error: the bytes end inside a value`; the launch refuses the fifth and the sixth before Cloud Hypervisor starts, and Cloud Hypervisor started without the launch shows only `reflect: the program given at boot is too large` for each

#### Scenario: Valid data at the limit fits the machine

- GIVEN byte forms of 2 MiB: one array of zeros, arrays of one nested around 0, a literal array of empty texts, a literal text of line ends, and a list of 419429 zeros written out as a program
- WHEN the image boots with each through the launch, the list with the budget 1000 and one interpreter
- THEN each serial stream is what the Linux process prints for the same bytes followed by `reflect: exit 0`: `bytes error: the value is not a program` twice, the two answers, and `no result within 1000 steps`; none ends in `INTERNAL PANIC: out of memory`, and at 4 MiB the literal array of empty texts does

#### Scenario: A literal nested deeper than the stack once held

- GIVEN a literal of 2 MiB that is arrays of one nested around 0, 2097149 deep
- WHEN the image boots with it
- THEN the serial port shows what the Linux process prints, the 2097149 arrays around 0, and `reflect: exit 0`; the image of `d2171ce` reported a full stack (`homoiconic-q59.72`)

#### Scenario: Data and programs nested deeper than the stack once held

- GIVEN at boot a program that compares data a million arrays deep with itself, the 2000001 bytes of a million functions each inside the last at levels 0 and 1, and the list of 419429 zeros at level 0
- WHEN the image boots with each
- THEN the serial port shows what the Linux process prints, `1`, `<function>` twice and `no result within 1000 steps`, and `reflect: exit 0`; the image of `d2171ce` reported a full stack for each

#### Scenario: A file that would land on the image

- GIVEN a file 4 KiB smaller than the 512 MiB first memory region
- WHEN it is given to the launch, and to Cloud Hypervisor directly
- THEN the launch refuses it and does not start Cloud Hypervisor; started directly, the serial port says nothing and Cloud Hypervisor reports an internal error from the processor

#### Scenario: Two files, and a module list outside memory

- GIVEN images that see the one file Cloud Hypervisor hands over as two files, or see the module list outside usable memory
- WHEN each boots with the factorial byte form
- THEN they show only `reflect: more than one file was given at boot` and `reflect: the list of files given at boot is not in usable memory`

#### Scenario: Nothing given

- GIVEN the same image file
- WHEN it boots with no bytes given
- THEN it runs the program built into it, as before

### Requirement: The layer hands the file given at boot over once

The layer SHALL export `reflect_boot_take(out, capacity)`. It SHALL return the length of the file given at boot, or 0 when none was given or it was taken before. When the length is no more than `capacity` it SHALL copy the bytes to `out`; in every case it SHALL then clear its own copy and forget the file, so that `/boot/program` does not open afterwards (`unikernel/kernel.zig`). The one-program image SHALL NOT call it, so the requirement "One image runs a byte form given at boot" holds of that image unchanged: there the layer does not read or change the bytes. The network image calls it for its entity key (`openspec/specs/unikernel-net/spec.md`).

#### Scenario: The one-program image does not name it

- GIVEN `unikernel/out/reflect.elf`
- WHEN `unikernel/check.sh` lists the kernel symbols the program names
- THEN `reflect_boot_take` is not among them, and the cases for a program given at boot pass as before

### Requirement: A run on the image has a space limit

The image SHALL pass a space to `reflect_run` and `reflect_interp`: the kernel's default (`reflect_default_space`), or the third word of the command line, `[step-budget [levels [space]]]`, a whole number below 2^64. A word that is not such a number SHALL end the image with a line of its own and `reflect: exit 2`. A run that passes its space SHALL end in the kernel's text, `no result within <space> cells`, and `reflect: exit 0`, as a run out of steps does, and SHALL NOT end in `INTERNAL PANIC: out of memory`. The default SHALL be a limit under which, on a 512 MiB machine started by `given.sh`, each of these ends in the kernel's text at the budget 100000000 at levels 0, 1 and 2: `def deep x = [x, ...deep x]`, `def build acc = build [0, ...acc]`, a text of 2 million characters whose `codes` is kept and that is then consed onto, an array of 2 million numbers of 19 digits answered, and an answer built by doubling. Where the budget ends such a run before it holds that much (`deep` through two interpreters, `build` through one or two), the budget's text is the kernel's text too. A machine with other memory is given another space by whoever starts it; the space is not in proportion to the machine's memory, since the image and the program are fixed costs (`unikernel/README.md`). The limit bounds what a run makes; what the program's bytes cost to read is bounded by the byte limit, as before.

#### Scenario: A recursion that waits, given at boot

- GIVEN the byte form of `def deep x = [x, ...deep x]` applied to 0
- WHEN `given.sh` boots it with `100000000 0` and with `100000000 1`
- THEN the serial port says `no result within 4000000 cells` and `reflect: exit 0`, the same as the Linux process

#### Scenario: A smaller space on the command line

- GIVEN the same bytes
- WHEN `given.sh` boots it with `100000000 2 100000`
- THEN the serial port says `no result within 100000 cells`

#### Scenario: The limit undone

- GIVEN the same bytes
- WHEN `given.sh` boots it with `100000000 0 18446744073709551615`
- THEN the image ends in `INTERNAL PANIC: out of memory`: the limit, not the budget, is what stops it
