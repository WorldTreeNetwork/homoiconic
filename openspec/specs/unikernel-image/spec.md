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

When Cloud Hypervisor is started with `--initramfs <file>`, the image SHALL treat that file's bytes as one program's byte form (`wire-bytes`). It SHALL pass exactly those bytes to `reflect_interp` with the byte-form flag set and the text flag clear, SHALL write the text that comes back to the serial port followed by a line end, and SHALL power the machine off. The PVH command line SHALL be `[step-budget [levels]]`: the budget SHALL default to the one built into the image and the levels to 1; level 0 runs the program itself and level k runs it through k interpreters. The program built into the image SHALL NOT run when bytes are given. One image file SHALL serve any number of different byte forms, one per boot, without being built again.

The layer SHALL move the bytes out of the memory the stack and the allocators will use before it lays those out, SHALL NOT hand that memory out while the bytes are still read from it, and SHALL NOT read or change the bytes. Non-Lean code SHALL NOT decide whether the bytes are a program: bytes the kernel refuses SHALL end in the kernel's text and `reflect: exit 0`. More than 16 MiB of bytes, or more than one boot module, SHALL stop the image with a line saying so before the C library starts. A budget or a level count that is not a whole number SHALL end in a line saying so and `reflect: exit 2`. The Linux comparison process SHALL take the same file and the same words, `reflect-linux <bytes-file> [step-budget [levels]]`, and call the same export.

#### Scenario: Two programs, one image

- GIVEN one image file, built once, and the byte forms of `examples/factorial.hom` and of a program whose answer is a text
- WHEN Cloud Hypervisor boots that file once with each byte form given at boot
- THEN each serial stream is byte for byte what the Linux process prints for the same bytes followed by `reflect: exit 0`, the factorial stream shows `265252859812191058636308480000000`, and the image file's hash is unchanged between the boots

#### Scenario: Levels and budget come from the command line

- GIVEN the factorial byte form and the byte form of `examples/forever.hom`
- WHEN the image boots with factorial and command lines naming 0, 1 and 2 levels, and with forever and the command line `5000`
- THEN factorial's answer is the same at every level, and forever shows `no result within 5000 steps`

#### Scenario: Bytes that are no program, and too many bytes

- GIVEN a megabyte of bytes that is no program, a program's byte form with one byte added, and a file of 16 MiB and one byte
- WHEN the image boots with each
- THEN the first two end in the text the Linux process prints for them and `reflect: exit 0`, and the third shows only `reflect: the program given at boot is too large`

#### Scenario: Nothing given

- GIVEN the same image file
- WHEN it boots with no bytes given
- THEN it runs the program built into it, as before
