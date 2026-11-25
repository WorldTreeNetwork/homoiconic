# One program in a Cloud Hypervisor image

Build on Linux x86_64 with Lean 4.35.0 (elan), Zig 0.16.0 on PATH,
GNU objcopy and sha256sum. Boot/check also needs KVM, timeout and nm.

```sh
sh unikernel/build.sh examples/factorial.hom
cloud-hypervisor --kernel unikernel/out/reflect.elf --cpus boot=1 --memory size=512M --serial tty --console off
CLOUD_HYPERVISOR=/path/to/cloud-hypervisor sh unikernel/check.sh
```

The supported hypervisor is 54.0. The ELF includes the Lean runtime, GMP,
Lean's C++ runtime, Zig's musl 1.2.5, boot code and a Zig syscall layer.
There is no Linux guest, firmware or disk. The source and step budget are
embedded at build time (optional second argument, default 100000000 steps).
Lean reads, compiles, evaluates and renders. Non-Lean code passes bytes.
Successful execution prints the result, then `reflect: exit 0`, and powers off.
This image has no network interface; the network image is `build-net.sh`.

## A program given at boot

The same `reflect.elf` runs any program handed to it at boot as its byte form.
It is not built again for each one.

```sh
unikernel/out/reply source examples/factorial.hom > factorial.bytes
CLOUD_HYPERVISOR=/path/to/cloud-hypervisor sh unikernel/given.sh factorial.bytes 100000000 1
unikernel/out/reflect-linux factorial.bytes 100000000 1     # the same, as a Linux process
```

`given.sh` starts Cloud Hypervisor with `--initramfs factorial.bytes
--cmdline "100000000 1"`, one processor and 512 MiB. Use it rather than
starting Cloud Hypervisor by hand: it refuses a file larger than 2 MiB before
the hypervisor starts. Cloud Hypervisor 54.0 copies the file to the top of the
first memory region without looking at where the image lies, so a file nearly
as large as the memory lands on the image before any of the image's code runs,
and the image cannot refuse it. On morphie a file of 500 MiB, or of 512 MiB
less 4 KiB, gave an empty serial port, `InternalError` from the processor and
exit status 0.

The command line is `[step-budget [levels [space]]]`, at most 1023 bytes; a
longer one stops the image with a line instead of being cut. The budget is a whole number
below 2^64 and defaults to the one built in. The levels are a whole number from
0 to 8 and default to 1: the bytes run through `reflect_interp`, the
interpreter written in the language, on the machine. Level 0 runs the program
itself; level 2 runs the interpreter in the interpreter. The kernel builds the
tower before the budget counts a step, so the levels are bounded by the
kernel (`Surface.maxLevels`, which `main.zig` asks for by `reflect_max_levels`),
not by the budget. A word that is not a number, and a number past these
limits, each end in a line of their own and `reflect: exit 2`. The space is
the cells the run may make, a whole number below 2^64, and defaults to the
kernel's, 4000000 (see "A run's space"). With no `--initramfs` the image runs
the source built into it through `reflect_run`, with the kernel's space.

`--initramfs` is only how Cloud Hypervisor carries a file into guest memory;
there is no file system. The layer finds the bytes as the one PVH boot module,
moves them to just above the image before it lays out the stack and the
allocators (the hypervisor puts them where the stack goes), clears where they
were, and serves them as the read-only file `/boot/program`. It starts the
program with `reflect /boot/program` and the command line's words. It does not
read the bytes: bytes that are no program are refused by the kernel, in the
kernel's text. The kernel's reader walks the bytes once without building
anything before it builds the value, so bytes that open millions of arrays and
never close them are refused at once as `bytes error: the bytes end inside a
value`. More than 2 MiB, a second module, or a module list outside usable
memory stops the image with a line. Cloud Hypervisor hands over one module at
most; the check reaches the last two lines with `PRETEND=two_modules` and
`PRETEND=module_list_outside`.

### Why 2 MiB

The limit is what the bytes may cost, measured on morphie with the image
started by `given.sh` (512 MiB) and, for peak memory, the Linux process.
Each shape filled the size given; a literal is `82 02` and then the data, a
program whose answer is the data, so the data is read, run and printed.

| shape | 4 MiB | 2 MiB |
|---|---|---|
| one array of zeros, or nested arrays of one, as data | kernel's text | kernel's text |
| literal: array of zeros, of names, a text of `a` | answer (up to 227 s of serial output) | answer |
| literal: array of empty texts, of empty arrays, a text of line ends | `INTERNAL PANIC: out of memory` | answer (243 MiB peak as a Linux process) |
| list of zeros written out (`[0, 0, ...]`), 1000 steps, 1 to 8 levels | | `no result within 1000 steps` (at most 132 MiB as a Linux process) |
| literal nested arrays | full stack | full stack (from 262144 deep; 131072 answers); since `homoiconic-q59.72` the answer, 2097149 deep |
| one number of 2 MiB (tag 2) | | `error: unbound` and 5050431 digits in 92 s, most of it the serial port (since `homoiconic-q59.64`; before, no answer in 300 s, 12 MiB) |

At 16 MiB one array of zeros ran out of memory as data. 2 MiB is the largest
power of two at which every shape here gave its answer or the kernel's text.
Two limits were not the byte limit's. A literal nested deeper than the stack
held ended in the report of a full stack, as a deep source does; since
`homoiconic-q59.72` the printer, the comparison, reading a program back and
compiling it are walks with their work on the heap, and the literal of 2 MiB
nested 2097149 deep is printed (the image of `d2171ce` filled its stack at
about 175000 levels, `evidence/q59.72-measurements.log`). A deep source still
fills the stack: the reader recurses. A number of
megabytes was read (`takeBE`) and printed in time that grew with the square of
its length: one of 128 KiB took 393 s as a Linux process. Since
`homoiconic-q59.64` each path splits the number in halves at a power of the
base, and the largest number the limit holds, tag 2 over 2097146 bytes of
`ff`, is read, run and printed in 92 s in the image, most of it 5 MB through
the serial port (`check.sh`).

The limit bounds what the bytes cost, not what a run costs. Until
`homoiconic-q59.65` a run's memory grew with its steps even when nothing was
kept: every call and case in tail position pushed a frame that only ended the
block again. `examples/forever.hom`, 52 bytes, ran the image out of memory at
the default budget of 100000000 steps at levels 0 and 1 (1151 MiB at level 0
as a Linux process), and the list of zeros above, at 1 MiB through one
interpreter, did after a few seconds of steps. A tail call now keeps no frame.
Measured on morphie (2026-11-24, tree `8300d8f`; the control is the same tree
with `kernel/` from `e9a4c86`; `reflect-linux` peaks from `getrusage`, the
image booted through `given.sh` with 512 MiB):

| run | 1M steps | 10M | 30M | 100M | image, 100M |
|---|---|---|---|---|---|
| forever, levels 0, 1, 2 | 11 MiB | 11 MiB | 11 MiB | 11 MiB | `no result within 100000000 steps` at each level |
| forever, level 0, a frame per tail call (control) | 19 MiB | 121 MiB | 349 MiB | 1151 MiB | `INTERNAL PANIC: out of memory` |
| forever, level 1, control | 11 MiB | 53 MiB | 145 MiB | 463 MiB | `INTERNAL PANIC: out of memory` |
| forever, level 2, control | 11 MiB | 19 MiB | 45 MiB | 135 MiB | `no result within 100000000 steps` |
| list of zeros, 1 MiB, one interpreter (before the space limit; see below) | 64 MiB | 176 MiB | 317 MiB (answer) | 317 MiB (answer) | the answer |
| the same, control | 68 MiB | 228 MiB | 463 MiB | 461 MiB (answer) | `INTERNAL PANIC: out of memory` |
| `def deep x = [x, ...deep x]`, 55 bytes | 15 MiB | 91 MiB | 259 MiB | 849 MiB | `INTERNAL PANIC: out of memory` |

What a run keeps live still grows with its steps where the program keeps it:
a recursion whose calls wait on each other keeps a frame per pending call
(`depth_bound` allows one a step), and built data is kept. `deep` is such a
run, and no byte limit or budget limit stops it. What stops it is the space
limit (`homoiconic-q59.67`, next section). The network image takes at most
1176 program bytes (a 1200-byte frame less its 24-byte header) and a budget of
at most 100000000 steps, so what its bytes cost is small; forever at
100000000 is the budget reply and the guest answers after it (`check-net.sh`).

## A run's space

A run has a space limit beside its step budget: the cells it may make. A cell
is one object of the run's state: a list cell, a closure, a frame, a box
around a number or an array, at most 24 bytes. The kernel counts the cells
each step makes in a ledger (`Reflect.runSpace`). When the ledger is spent it
asks how many cells the state holds, each object counted once
(`reflect_live_cells`, a walk by address); at most three quarters of the
limit, and the run goes on with the difference; more, and the run ends with
the kernel's line, `no result within <cells> cells`, and `reflect: exit 0`, as
a run out of steps ends. On the network image the reply is `81 07`, beside the
budget reply `81 01`, and the guest answers the next request.

The limit comes from whoever starts the machine, not from whoever sends a
program:

```sh
sh unikernel/given.sh deep.bytes 100000000 0            # the kernel's default, 4000000 cells
sh unikernel/given.sh deep.bytes 100000000 2 100000     # 100000 cells, through two interpreters
cloud-hypervisor ... --cmdline "reflect.ip=... reflect.port=4444 reflect.space=2000000"
unikernel/out/reply run 100000000 deep.bytes 100000     # the same export, as a Linux process
```

The `RFL1` frame is unchanged. A guest of a crossing runs each turn with the
kernel's `turnSpace` whatever `reflect.space` says, so its record replays the
same elsewhere; what such a guest holds between turns is not bounded
(`homoiconic-q59.71`).

An answer is checked before it is written. A value is written as the tree it
is, which can be far more than the cells it holds: forty cells built by
doubling are 2^40 bytes, and a function's byte form writes each environment
where it is held. An answer that would take more than four bytes written for
each cell of the space, 16 MB for the default, ends in the same line or reply.
An item of an array is counted five bytes and itself, three more than it
writes, because the printer's memory goes by items (about 75 bytes for each
while it prints); so an answer has at most 2.28 million items, however they
are held.

### Why 4000000 cells

The image has less than its 512 MiB for a run: `kernel.zig` gives a quarter of
what lies between the image and the stack to `brk` and the rest, about 360
MiB, to `mmap`, where Lean's allocator and the walk's table come from. Against
that, for a limit of `n` cells: at most `24 n` bytes of state; for a moment,
the answer an operation makes before it is charged (at worst two cells and a
spare list cell for each character of a text the run holds); the walk's own
table and stack, at most `17 n` bytes while a count runs; the program itself,
up to about 100 MiB for a 2 MiB literal at boot; and the answer written. The
limit is not in proportion to a machine's memory, since the image and the
program are fixed costs: a guest with other memory is given a limit from this
sum against its own `mmap` area.

Measured on morphie (2026-11-25 UTC, tree `48327f6`; `evidence/q59.67-measurements.log`), each run with the budget
100000000: as the Linux process `out/reflect-linux`, with its peak from
`getrusage`, and on the image started by `given.sh` with 512 MiB.

| run | Linux process | peak | image |
|---|---|---|---|
| factorial, through 0, 1, 2 interpreters | the answer | 12 MiB | the answer |
| forever, through 0, 1, 2 | `no result within 100000000 steps` | 12 MiB | the same |
| `def deep x = [x, ...deep x]`, through 0 | `no result within 4000000 cells` | 116 MiB | the same |
| the same, through 1 | `no result within 4000000 cells` | 104 MiB | the same |
| the same, through 2 | `no result within 100000000 steps` (270046 cells held at the end) | 23 MiB | the same |
| the same, through 2, space 100000 | `no result within 100000 cells` | 12 MiB | the same |
| `def build acc = build [0, ...acc]`, through 0 | `no result within 4000000 cells` | 115 MiB | the same |
| the same, through 1 and 2 | `no result within 100000000 steps` (101274 and 4974 cells) | 12 MiB | the same |
| the same, through 1, space 100000 | `no result within 100000 cells` | 12 MiB | the same |
| an answer built by doubling forty times | `no result within 4000000 cells` | 12 MiB | the same |
| 800000 numbers of 19 digits answered | `no result within 4000000 cells` | 35 MiB | the same |
| 590000 numbers of 19 digits answered | the answer, 12390001 bytes | 107 MiB |  |
| 2200000 empty texts answered, the most items an answer may have | the answer, 8800001 bytes | 168 MiB |  |
| an array of 1000 zeros held 3990 times, 21000 cells | `no result within 4000000 cells` | 12 MiB | the same |
| the same held 2000 times | the answer, 6004001 bytes | 50 MiB |  |
| a text of 1200000 characters, its `codes` kept, one `cons` onto it | `no result within 4000000 cells` | 121 MiB | the same |
| a number squared again and again | `no result within 100000000 steps` (the product's cost stops it) | 12 MiB |  |
| a list of 30000 items written out, through 1 | the answer | 105 MiB |  |
| `deep` behind a literal of 2 MiB (2097100 empty texts) | `no result within 4000000 cells` |  | the same |
| `deep` through 0, with the largest space there is | `no result within 100000000 steps` | 849 MiB | `INTERNAL PANIC: out of memory` |

Over UDP (`check-net.sh`), `deep`, `build`, the doubled answer and a function
answered from thirty definitions are each `81 07` at the budget 100000000, the
Linux export's reply, and factorial is answered after each. A guest started
with `reflect.space=18446744073709551615` runs out of memory on `deep` and
answers nothing more, as every guest did before the limit.

One run the table under "Why 2 MiB" records no longer answers: the list of
209715 zeros written out, 1 MiB, through one interpreter. It holds 3.7 million
cells of program as data before it starts, more than three quarters of the
default, and ends in the space line at its first count. It took 317 MiB of the
360 MiB the image has; a run that large is past any limit that protects the
image. A larger space on the command line runs it.

What the limit costs in time, the same runs built from this tree and from
`451a5de` (`out/reflect-linux`, the best of three, what starting the process
takes subtracted):

| run | steps | before, steps a second | after | time |
|---|---|---|---|---|
| factorial, through 1 interpreter | 55543 | 16.9 M | 14.9 M | +12.9% |
| factorial, through 2 | 4036172 | 17.2 M | 15.4 M | +12.0% |
| forever, through 0 | 100000000 | 20.3 M | 18.8 M | +8.3% |
| forever, through 1 | 100000000 | 17.6 M | 15.8 M | +11.6% |
| forever, through 2 | 100000000 | 17.6 M | 15.9 M | +10.9% |

Factorial itself is 1165 steps, a twentieth of a millisecond, too short to
time this way. The cost is the ledger on every step; a count happens once in
millions of steps and does not show. With the charge read from the state
before and after each step, as first written, it was 40% (measured on the Mac);
charging before the step, so that `step` is given the state to use up, is what
brought it to this.


`build.sh` runs Lake, compiles generated C for Surface.Host's local imports,
and links identical Lean objects into `out/reflect.elf` and
`out/reflect-linux`: exactly the objects `objects.sha256` names, not whatever
lies in `out/lean`. It does not use host/check.sh or host/out artifacts.
`versions.txt`, `source.sha256` and `objects.sha256` record provenance.
Source/toolchain or object changes reject reuse: remove `unikernel/out`
and rebuild. Build outputs are ignored. Checks start from an empty output
folder and compare full serial streams against the Linux executable and
independent expected values, including a rendering larger than 64 KiB.

## An entity's key (the network image)

A guest that serves or calls over QUIC runs for one entity and has that
entity's Ed25519 key. The key is not in the image: one `reflect-net.elf`
serves every entity. The key is a 32-byte file its owner makes and keeps, and
the name is computed from the file alone.

```sh
head -c 32 /dev/urandom > guest.key && chmod 600 guest.key   # the owner's; keep it
unikernel/out-net/entity name guest.key                       # its name, base58
cloud-hypervisor --kernel unikernel/out-net/reflect-net.elf --initramfs guest.key \
    --cpus boot=1 --memory size=512M --serial tty --console off --net tap=... \
    --cmdline "reflect.ip=... reflect.port=4444 reflect.quic_port=4445 reflect.allow=<client name>"
unikernel/out-net/quic-client <ip> 4445 <budget> <program-file> client.key <guest name>
```

The name is identikey-protocol's fingerprint of the key: Blake3 of the dCBOR
of `{"alg": "ed25519", "key": <public key>}`, written in base58
(`unikernel/entity.zig`). The guest prints `reflect: entity <name>` before
`reflect: ready`. `reflect.allow` is the list, one to eight names, of the
entities it finishes a handshake with; each end proves its key and checks the
other's name. With a QUIC word and no key the guest prints `reflect: no entity
key` and powers off; there is no built-in key. Such a guest answers nothing on
its plain UDP port.

Whoever starts the guest holds the key: they chose its memory and can read
it. Giving the key as a file keeps it out of the image, its hash, the process
list and the hypervisor's log, and no more. Never put it on the command line.

## Who a QUIC guest admits

A guest with `reflect.quic_port` or `reflect.wire_port` keeps up to 12 server
connections (`unikernel/admit.zig`): 4 for first flights that show nothing and
8 for first flights that answered a Retry, at most one handshake in progress
there per IPv4 address. Nothing is evicted. A connection not accepted 2 s after
its first Initial leaves, whatever it sends; an accepted one leaves when its
reply is acknowledged or given up, or after 2 s with nothing in flight and
nothing opened. When the first pool is full a first Initial that opens is
answered with a 71-byte Retry and nothing is kept; the client's next Initial
carries the token (its address, port and the Retry's ID under the guest's key,
good for 10 s) and goes to the second pool. A connection is 70360 bytes; the
table is 844736. Packets whose number was opened before do not count. The
property, its assumptions and what a host on the path can still do are in
`openspec/specs/unikernel-net/spec.md` ("A host with no allowed key cannot
shut an allowed client out").

What a flood costs, measured on morphie on 2026-11-25 UTC (`quic-self`'s
code built for that host, then a guest):

| | Time |
|---|---|
| A first Initial checked and answered with a Retry (host, baseline x86_64, ReleaseSmall as the guest is built) | 66 µs to open, 3 µs for the Retry |
| The same, ReleaseFast; with AES-NI and PCLMUL as well | 45 µs + 2 µs; no faster with the instructions |
| A first Initial admitted (the server's first flight: X25519 twice, an Ed25519 signature) | 270 to 390 µs |

A guest flooded from a second address with the mix of `quic-client ... flood`
(a third new first flights, a third one first flight again, a third the
datagrams of a finished exchange), four allowed clients timed in each run:

| Datagrams a second | Allowed clients served in | Retries the flooder heard a second |
|---|---|---|
| 1000 | 6, 6, 6, 7 ms | 371 |
| 2000 | 6, 6, 7, 5 ms | 702 |
| 5000 | 11, 9, 7, 7 ms | 1755 |
| 10000 | 694, 1708, 455, 414 ms | 2614 |
| 20000 | 700, 786, 1524, 514 ms | 2285 |
| as fast as one host process sends (about 220000) | 7645 ms (gave up), 5, 5, 5 ms | 2649 |

So the guest keeps up with about 5000 datagrams a second of this mix (about 6
MB/s) and falls behind by 10000, where it answers about 2600 Retries a second;
past that the host's TAP queue (1000 datagrams) drops without regard to
sender, and allowed clients wait for their resends. That is the rate under
which the property's first assumption holds on this host. Under it the queue
ahead of a client's datagram is at most the 8 receive buffers and the TAP queue
at about 0.37 ms each, under 0.4 s, so its two datagrams before acceptance fit
the 2 s cap. `check-quic.sh` floods at 4000 a second (`FLOOD_RATE`). Building
the network layer ReleaseFast would buy about a third; it was not done here.

## Runtime audit (Lean v4.35.0)

The permitted entry is `main.zig` -> module initializer ->
`kernel_finish_initialization` in `host/runtime.c` -> `reflect_run` in
`kernel/Surface/Host.lean`, or `reflect_interp` there when bytes were given
at boot (`Surface.interpBytes`: decode, lift, run the bounded machine, render;
synchronous like the first). That export copies input bytes, calls
`Surface.runText`, and stores rendered bytes. The Surface.Run path reads,
compiles, runs the bounded Reflect machine with arithmetic, and renders;
it has no asynchronous IO or task execution. Imports must be re-audited
when they change; the image does not support arbitrary Lean exports.

Upstream pinned sources:

- [init_module.cpp](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/init_module.cpp): runtime initialization remains intact except its final libuv initialization.
- [libuv.cpp](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/libuv.cpp): the substituted initializer skips timer/socket/signal/loop facilities and the loop thread. This is safe only for the permitted synchronous path.
- [thread.cpp](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/thread.cpp): initialize_thread creates bookkeeping; spawning an lthread would create a worker and is unsupported.

The build weakens initialize_libuv in a copied archive; main's empty
function wins. The check verifies its resolved address. Other thread and
libuv symbols can remain linked without being called. A syscall not served
prints its number and returns ENOSYS; unexpected diagnostics fail the suite.
Signal setup is acknowledged but Linux signals are not delivered. Hardware
faults use the image's IDT/TSS, rather than Lean's signal handler.

## CPU and stack limits

One vCPU, one thread, interrupts disabled. XSAVE and RDRAND are required;
missing features produce a diagnostic before entering musl. Only x87/SSE
and optional AVX are enabled (XCR0 3 or 7); the save area is checked against
4096 bytes and aligned to 64. The syscall entry preserves the red zone,
flags and register/vector state. The suite boots a deliberate clobbering
handler to test this boundary.

The 16 MiB stack has an unmapped 2 MiB guard, excluded from both allocators.
Page/stack/double faults use a separate 64 KiB fault stack. The guarantee
covers contiguous growth touching the guard, including syscall save space;
it does not cover arbitrary unchecked allocations that jump over 2 MiB.
The guard probe checks a fault at its named address and an intact sentinel
below it. A separate deeply nested source must fault on the alternate stack:
the source reader is the one part of the kernel that still recurses on
nesting. Data, programs given as bytes, code and functions do not
(`homoiconic-q59.72`, `kernel/WalkContract.lean`).
The entire address space is privileged and writable: this is not a security
boundary against arbitrary native code.

RDRAND results are used only on successful carry status, at most ten tries.
Failure stops with a diagnostic. AT_RANDOM, getrandom and /dev/urandom share
that source. Test-only options inject absence/failure; they do not implement
a fallback. Time is an uncalibrated tick-counter stand-in; the stopped-clock
check establishes that the tested language result does not depend on it.

All boot code, syscall services, libc, compiler/runtime and hypervisor are
trusted infrastructure outside the Lean semantics proofs.

## Recorded validation

2026-11-12 on morphie, Linux x86_64/KVM, Cloud Hypervisor 54.0.
`evidence/check.log` records the clean current-source suite; version, source
and compiled-object manifests are beside it. `negative-controls.log` records
failed preservation after removing vector restore or red-zone skipping,
rejected stale provenance and a corrupt object, and the final restored
factorial boot. The Framework laptop was unreachable in the earlier session;
these results are from morphie, not the Framework.

2026-11-18: morphie is the build and check host (confirmed after homoiconic-q59.40).
`CLOUD_HYPERVISOR=~/ch54/cloud-hypervisor sh unikernel/check.sh` on morphie,
Linux x86_64/KVM, Cloud Hypervisor 54.0. The Framework laptop still times out
over SSH; do not wait on it for an image rebuild.

2026-11-19 on morphie, Cloud Hypervisor 54.0: `unikernel/check.sh` passed with
the cases for a program given at boot (`evidence/check-boot-bytes.log`, 33
lines of `ok`). One `reflect.elf`, hashed before and after, ran the byte forms
of text, factorial at 0, 1 and 2 levels, the quine and a 5000-step budget, each
equal to the Linux process. `unikernel/check-net.sh` passed after it, unedited.

2026-11-23 on morphie, Cloud Hypervisor 54.0, tree `c0c800c` exported with
`git archive` to `~/hom-c0c800c`: `build.sh examples/factorial.hom`,
`build-net.sh`, `check.sh`, `check-net.sh`, `check-quic.sh` and `check-wire.sh`
each exited 0. Their logs are `evidence/build.log`, `build-net.log`,
`check.log`, `check-net.log`, `check-quic.log` and `check-wire.log`, with the
exit codes and image hashes in `evidence/run-c0c800c.txt`; `source.sha256`,
`objects.sha256` and `versions.txt` are the ones that build wrote.
`reflect-net.elf` is sha256 `babd599f…f302ec`, the same before and after the
checks rebuilt it. `evidence/check-quic-controls.log` is `check-quic.sh` on a
copy of that tree with each fix of `homoiconic-q59.50` and `q59.53` undone in
turn; every one fails at its own step. A non-interactive `ssh morphie` has no
`zig` on its PATH: Zig 0.16.0 is at `~/.local/share/mise/installs/zig/0.16.0/bin`.

2026-11-24 (UTC) on morphie, Cloud Hypervisor 54.0, tree `9de1838` exported
with `git archive` to `~/hom-9de1838`: `build.sh examples/factorial.hom`,
`build-net.sh`, `check.sh`, `check-net.sh`, `check-quic.sh` and `check-wire.sh`
each exited 0. The six logs in `evidence/` are now this run's (those of
`c0c800c` are in git at `709b13a`), with the exit codes and image hashes in
`evidence/run-9de1838.txt`; `source.sha256`, `objects.sha256` and
`versions.txt` came out the same as that build wrote before, since the Lean
side did not change. `reflect-net.elf` is sha256 `1f3aa81c…b9718c`, the same
before and after the checks. `check-quic.log` has fourteen `ok` lines; the
guest sent 8 more copies of an unacknowledged reply and stopped at 6.3 s, and
sent 3568 bytes in 8 datagrams for a forged first flight of 1200.
`evidence/check-quic-controls-q59.56-57.log` is `check-quic.sh` on a copy of
that tree with each fix of `homoiconic-q59.56` and `q59.57` undone in turn and
the build told to go on past a failing `quic-self`, so both the `quic-self`
exit and the guest step that fails are there. The old acknowledgement rule
fails `quic-self` (exit 21) and no guest step.

2026-11-23 on morphie, Cloud Hypervisor 54.0 (`homoiconic-q59.60`):
`evidence/boot-bytes-controls.log` shows each finding of the cross-family
review on an image built from `709b13a`, before the fixes: 16 MiB of bytes
`81` ran out of memory, 4294967295 levels at budget 0 faulted on a full stack,
a cut command line read as budget 0, and 500 MiB or 512 MiB less 4 KiB given
at boot silenced the image while Cloud Hypervisor exited 0. On the fixed tree
a stray object in `out/lean` was not linked, 4 Mi nested arrays were refused
in the kernel's text, and 8 Mi nested arrays or a flat 16 MiB array still ran
out of memory (`homoiconic-q59.61`). Tree `79faa08` (these fixes rebased on
`f1ff2f6`), exported with `git archive` to `~/hom-79faa08`: `build.sh
examples/factorial.hom`, `build-net.sh`, `check.sh`, `check-net.sh`,
`check-quic.sh` and `check-wire.sh` each exited 0. Their logs are
`evidence/boot-bytes-79faa08-*.log` (`check.sh`'s has 52 lines of `ok`), with
exit codes and image hashes in `evidence/run-79faa08.txt`; the QUIC run's
logs beside them are left as they were. `source.sha256`, `objects.sha256`
and `versions.txt` are the ones this build wrote.

2026-11-24 (UTC) on morphie, Cloud Hypervisor 54.0 (`homoiconic-q59.58`,
`q59.59`, `q59.62`), tree `e275842` exported with `git archive` to
`~/hom-e275842`: `build.sh examples/factorial.hom`, `build-net.sh`,
`check.sh`, `check-net.sh`, `check-quic.sh` and `check-wire.sh` each exited 0.
The six logs in `evidence/` are this run's, with exit codes and image hashes
in `evidence/run-e275842.txt`; `source.sha256` and `objects.sha256` are the
ones this build wrote (the Lean side changed). `reflect-net.elf` is sha256
`4c66c447…ae82ea`, the same before and after the
checks. `check-quic.log` has eighteen `ok` lines: the guest's answer to a
first flight is 1200 bytes, a reply the client acknowledges went out once,
a `silent` client's reply was sent 9 more times and stopped at 6.3 s, and a
forged first flight of 1200 bytes drew 3 datagrams and 3600 bytes.
`evidence/check-quic-controls-q59.58-59.log` is `check-quic.sh` on copies
of the tree before commit with each fix undone: no ACK-only packet fails
`quic-self` (exit 20) and the guest sends the reply 13 times in the counted
window; a client that does not acknowledge leaves 13; no padding fails
`quic-self` (exit 29) and the guest's first answer is 748 bytes.
`evidence/levels-controls-q59.62.log` shows the level bound undone on each
side, on the Mac. The first export of these fixes, `2fc1ec2`, failed
`check.sh` at the list of kernel symbols the program names, which now
includes `reflect_max_levels` (fixed in `e275842`).

2026-11-24 (UTC) on morphie, Cloud Hypervisor 54.0 (`homoiconic-q59.61`, the
limit lowered to 2 MiB), tree `f8a8759` exported with `git archive` to
`~/hom-f8a8759`: `build.sh examples/factorial.hom`, `build-net.sh`,
`check.sh`, `check-net.sh`, `check-quic.sh` and `check-wire.sh` each exited 0.
Their logs are `evidence/q59.61-f8a8759-*.log` (`check.sh`'s has 60 lines of
`ok`), with exit codes and image hashes in `evidence/run-f8a8759.txt`; the
other runs' logs are left as they were. `reflect.elf` built from factorial is
sha256 `f3c54a3e…dd1033`; `reflect-net.elf` is `33a04433…29f530`, the same
before and after the checks. `source.sha256`, `objects.sha256` and
`versions.txt` came out the same as before: the Lean side did not change.
`evidence/q59.61-measurements.log` has the measurements behind "Why 2 MiB".
`evidence/q59.61-limit-controls.log` is `check.sh` on copies of the tree with
the limit put back: at 16 MiB it fails at the one array of zeros, and at 4 MiB
at the literal array of empty texts, each with `INTERNAL PANIC: out of memory`.

2026-11-24 (UTC) on morphie, Cloud Hypervisor 54.0 (`homoiconic-q59.49`,
`add-entity-keys`), tree `e9a4c86` exported with `git archive` to
`~/hom-e9a4c86`: `build.sh examples/factorial.hom`, `build-net.sh`,
`check.sh`, `check-net.sh`, `check-quic.sh` and `check-wire.sh` each exited 0.
The six logs in `evidence/` are this run's, with exit codes and image hashes
in `evidence/run-e9a4c86.txt`; `source.sha256` and `objects.sha256` are the
ones this build wrote (the Lean side had changed under it). `reflect-net.elf`
is sha256 `562c8143…7fcac4c`, the same before and after the checks, and holds
no key. `check-quic.log` has twenty-six `ok` lines: a guest with no key, 31
bytes or 32 zero bytes serves no QUIC; a run request in a STREAM frame of an
Initial packet leaves a guest with `reflect.hook=alloc` running, and the
allowed client's request stops it; a guest with another key prints another
name and the client that expects the first refuses it; a client whose key is
not allowed is refused and the allowed client, started 0.1 s later, was served
in 8 ms; a ping to the plain UDP port of a QUIC guest is not answered; the
same key started again is the same name. `check-wire.log` has the two guests
with two keys, and both refusals. `evidence/entity-keys-controls.log` is
`evidence/entity-keys-controls.py` run on morphie on the tree before its
rebase (`95d7435` with the final `quic-self.zig`; the Zig files are the ones
of `e9a4c86`): twenty-nine controls, each fix undone in turn, nineteen in
`quic-self` and ten on real guests, and every one fails at its own step. With
the frame rule alone undone the guest step still passes, because the second
gate holds, and `quic-self` exits 68. `host/check.sh` passed on the Mac.

**2026-11-24, `add-recorded-crossing` (`homoiconic-q59.51`).** `check-wire.sh`
no longer sends one built-in program. Guest A (`reflect.wire_port`) is handed
a program's bytes over QUIC by `quic-client`; guest B (`reflect.peer`) starts
with no process and opens the exchanges. Starts and sends cross between them,
each guest prints its signed record on serial (`reflect: cross …` lines), and
`out-net/cross-check check <bytes> <record-a> <record-b>` combines the two
logs, replays the schedule on one machine and compares
(`openspec/specs/crossing/spec.md`). Final run on morphie from a
`git archive` export of `ecaa6c8` into `~/hom-ecaa6c8`: `build.sh
examples/factorial.hom`, `build-net.sh`, `check-net.sh`, `check-quic.sh`,
`check-wire.sh` and `check.sh` each exited 0; `check.sh` ran last and with
`CLOUD_HYPERVISOR=~/ch54/cloud-hypervisor`, because the first try found
v53.0 on the path and stopped before building anything. Logs are
`evidence/q59.51-ecaa6c8-*.log` (`check.sh` has 60 lines of `ok`,
`check-wire.sh` 27), exit codes and hashes `evidence/run-ecaa6c8.txt`.
`reflect-net.elf` is sha256 `f53a6a38…b10a9d`, the same before and after the
checks; `source.sha256`, `objects.sha256` and `versions.txt` are that run's.
`evidence/wire-ecaa6c8/` holds the two guests' records of each of the four
runs and what the check answered: `old.a` and `new.a` are one program
(`examples/cross-race.hom`) with `reflect.take=old` and `reflect.take=new`,
their last two entries are the two takings in the two orders, and they replay
to `[1, 2]` and `[2, 1]`. Keys are made on each run, so the names in those
records are that run's.
`evidence/build.log`, `build-net.log`, `check.log`, `check-net.log`,
`check-quic.log` and `check-wire.log` are copies of this run's logs: it is the
later tree, and holds `add-entity-keys` as `e9a4c86` had it.
`evidence/cross-controls.log` is `kernel/cross-controls.py` in that tree: one
check of the Lean side undone at a time in a copy of the kernel, and the test
credited to it failing. One rule is listed with no test, because undoing it
stops honest logs combining. The script there is the next commit's: the
`ecaa6c8` one had a control that gave no result in 300 seconds on morphie.
`evidence/cross-sig-controls.log` is `check-wire.sh` on copies of the tree
with each check of the record's signature undone in `cross-check.zig`.
The script is `evidence/cross-sig-controls.sh`. With the signature not verified the moved entry is caught by the link instead; a record with no signature and one signed by another entity are accepted.

**2026-11-24 (UTC), a tail loop's memory (`homoiconic-q59.65`).** On morphie,
Cloud Hypervisor 54.0, tree `f9f4c81` exported with `git archive` to
`~/hom-f9f4c81` (its `kernel/`, `unikernel/` and `host/` are those of the
commit that landed): `build.sh examples/factorial.hom`, `build-net.sh`,
`check.sh`, `check-net.sh`, `check-quic.sh` and `check-wire.sh` each exited 0.
Logs are `evidence/q59.65-f9f4c81-*.log` (`check.sh` has 63 lines of `ok`,
among them forever at the default budget through 0, 1 and 2 interpreters;
`check-net.sh` sends forever at 100000000 and gets `81 01`, then factorial),
exit codes and hashes `evidence/run-f9f4c81.txt`. `reflect.elf` built from
factorial is sha256 `1e84a6d5…dc462c5`; `reflect-net.elf` is `cdd58dc8…3690f0`,
the same before and after the checks. `source.sha256`, `objects.sha256` and
`versions.txt` are this build's (the Lean side changed). An earlier run of
`8300d8f` failed `check-net.sh` at the new case only because the client
stopped reading on its socket's 3-second timeout; the guest was up (fixed in
the next commit). `evidence/q59.65-measurements.log` has the numbers in the
table under "Why 2 MiB", for `8300d8f` and for the control, the same tree with
`kernel/` from `e9a4c86`; `evidence/q59.65-control-check.log` is `check.sh`
on that control, failing at `forever at the default budget through 0` with
`INTERNAL PANIC: out of memory`. `host/check.sh` passed on the Mac, and with
the baseline binary its new case fails at 1181376 KiB.

**2026-11-25 (UTC), a run's space (`homoiconic-q59.67`, `add-space-budget`).**
On morphie, Cloud Hypervisor 54.0, tree `48327f6` exported with `git archive`
to `~/hom-48327f6`: `build.sh examples/factorial.hom`, `build-net.sh`,
`check.sh`, `check-net.sh`, `check-quic.sh` and `check-wire.sh` each exited 0.
Logs are `evidence/q59.67-48327f6-*.log` (`check.sh` has 80 lines of `ok`,
`check-net.sh` 19 and the four space replies, `check-quic.sh` 26,
`check-wire.sh` 27), exit codes and hashes `evidence/run-48327f6.txt`.
`reflect.elf` built from factorial is sha256 `0562b1c0…d137c43b`;
`reflect-net.elf` is `bba55325…b62ee6cd`, the same before and after the
checks. `source.sha256` and `objects.sha256` are this build's (the Lean side
changed); `versions.txt` came out the same. `check.sh` boots `deep` and
`build` at 100000000 steps: each ends in `no result within 4000000 cells`,
equal to the Linux process, and with the largest space on the command line
`deep` ends in `INTERNAL PANIC: out of memory`, as it did before the limit.
`check-net.sh` gets `81 07` for `deep`, `build`, the doubled answer and a
function from thirty definitions, each equal to the Linux export's, factorial
after each, and a guest started with `reflect.space=18446744073709551615` runs
out of memory. `evidence/q59.67-measurements.log` has the peaks and the times
in the tables under "Why 4000000 cells". `evidence/q59.67-controls.log` is
`host/check.sh`, `check.sh` and `check-net.sh` on a copy of the tree
(`~/hom-48327f6-undone`) whose one change is that `reflect_default_space`
answers the largest space: `host/check.sh` fails at `deep` (the budget line
where the space line is wanted), `check.sh` at `a recursion that waits ends
out of space through 0` with `INTERNAL PANIC: out of memory`, and
`check-net.sh` with no reply to `deep` and the same panic on the guest's
serial port. `host/check.sh` passed on the Mac on the same tree, and ran on
morphie as far as that control's failure. An earlier export of the tree before
the read of the landed code (`761ef8a` with these checks, `~/hom-pre-9582bbf`)
passed `check.sh` and `check-net.sh`; its first try failed only at the
control's own assertion, which expected no `reflect: exit` line after the
panic, and the image prints `reflect: exit 1`.

**2026-11-25 (UTC), nesting deeper than the native stack (`homoiconic-q59.72`).**
On morphie, Cloud Hypervisor 54.0, tree `6662086` exported with `git archive`
to `~/hom-6662086`: `build.sh examples/factorial.hom`, `build-net.sh`,
`check.sh`, `check-net.sh`, `check-quic.sh` and `check-wire.sh` each exited 0.
Logs are `evidence/q59.72-6662086-*.log` (`check.sh` has 84 lines of `ok`,
`check-net.sh` 19, `check-quic.sh` 29, `check-wire.sh` 30), exit codes and
hashes `evidence/run-6662086.txt`. `reflect.elf` built from factorial is sha256
`b9c0c185…1938ab28`; `reflect-net.elf` is `f8ff101f…19f2b284`, the same before
and after the checks. `source.sha256` and `objects.sha256` are this build's
(the Lean side changed). New in `check.sh`: the 2 MiB literal nested 2097149
deep is printed, equal to the Linux process (it reported a full stack); data a
million deep compared with itself gives `1`; a million nested functions give
`<function>` through 0 and 1; the list of 419429 zeros compiled runs out of its
1000 steps. `check-net.sh` gets `82 00 82 00 01` for the 119-byte deep
comparison and factorial after it, status 2 for a deep answer, and status 2 for
a chain of 300000 functions on the guest with the space limit undone.
`check-wire.sh` runs `examples/cross-deep.hom` on two guests and the replay
accepts `process 1: 7; holds [#48]`. `evidence/q59.72-controls.log` is the
same checks on `~/hom-82abb4d-ctl`, tree `82abb4d` with `kernel/` from
`d2171ce`: each new boot case, the deep comparison over UDP, the chain of
functions and the crossing end in the report of a full stack; the deep answer
passes there too (writing data was a loop already). The depths at which the
old kernel filled the stack are in `evidence/q59.72-measurements.log`.
`host/check.sh` passed on the Mac, with output identical to the old tree's
apart from the new lines.

**2026-11-25 (UTC), the crossing hardened (`harden-crossing`: `homoiconic-q59.79`,
`q59.71`, `q59.69`).** On morphie, Cloud Hypervisor 54.0, tree `73fefe9`
exported with `git archive` to `~/hom-73fefe9`: `build.sh examples/factorial.hom`,
`build-net.sh`, `check.sh` (88 `ok`), `check-net.sh` (19), `check-quic.sh` (29)
and `check-wire.sh` (46, `wire guests ok`) each exited 0. Logs are
`evidence/harden-crossing-73fefe9-*.log`, exit codes and hashes
`evidence/run-73fefe9.txt`; `source.sha256` and `objects.sha256` are this
build's. `reflect-net.elf` is sha256 `3ba11a46…3424254`, the same before and
after the checks; `reflect.elf` built from factorial is `fbd45c8c…0fba4d4`.
(Another session extracted the same commit into that directory again while
`check-wire.sh` ran; the files were byte-identical and only their times moved.)
New in `check-wire.sh`: a calling guest that allows any budget, and one that
allows 50000 steps and 300000 cells, each run `cross-reply.hom` and both records
say what the lower allows (`budget 100000 500000`, `budget 50000 300000`). With
the default hold of 2000000 cells, `cross-grow-forever.hom` ends `full a: entry
791, 1500001 cells counted` (the count stops past the bar), `cross-fan.hom`
under `spawn=far` ends `full b: entry 211`, and `cross-chatter.hom`, a meeting
loop that holds nothing new, stops at its cap, `full a: entry 60000, 180439
cells counted`, a record of about 7 MB printed on serial; each record is
accepted and no guest stopped. `cross-worst.hom` makes the largest local start
built here on top of 1476097 cells counted, and the guest goes on. The same
growing process with `reflect.hold=18446744073709551615` ends guest A in
`INTERNAL PANIC: out of memory`. A run of `cross-hidden.hom` with its two local
deliveries swapped and signed again is refused at the root of process 0; A's
record of the `old` run with B's of the `new` run is refused by the order of the
acknowledgements. A first wire run of `788c69f` failed before any crossing: a
static 16 MiB record buffer in `.bss` kept QUIC from answering (the host client
gave up, exit 6); the same build with 256 KiB answered, and the buffer is now
taken from the heap (`0a5acac`). The 34 controls of `kernel/cross-controls.py`
are `evidence/harden-crossing-controls.log` (`controls ok`). `host/check.sh`
passed on the Mac on `788c69f`.

2026-11-25 UTC, on morphie, Cloud Hypervisor 54.0, tree `5107fa8` (add-quic-admission,
homoiconic-q59.63) exported with `git archive` to `~/hom-5107fa8` and built from
nothing: `build.sh examples/factorial.hom`, `build-net.sh`, `check-net.sh` (19
`ok`), `check-quic.sh` (29 `ok`, `quic guest ok`) and `check-wire.sh` (28 `ok`,
`wire guests ok`) each exited 0. Logs are `evidence/q59.63-5107fa8-*.log`, exit
codes and hashes `evidence/run-5107fa8.txt`; `source.sha256` and
`objects.sha256` are this build's, `versions.txt` came out the same.
`reflect-net.elf` is sha256 `72e641e6…b656fe4a`, the same before and after the
checks. In `check-quic.sh` five allowed clients were served in 7 to 10 ms each
while a second address flooded the guest at 4000 datagrams a second, an
allowed client was served in 15 ms behind four stalled clients on no list and
the client of `e9a4c86` (Mjolnir's) in about 2.5 s, after their cap; in
`check-wire.sh` a crossing closed while the host flooded the serving guest.
`check.sh` exited 1 at one step, `given deep.bytes: no power off within 60
seconds`, after 49 `ok`: the 2 MiB nested byte form that used to fill the
guest's stack (`the stack is full`) is now read and its answer printed, which
the step does not expect. That is the deep-walk change of the kernel
(`3e0635d`), not this one: nothing `check.sh` builds or boots was changed here.
Its serial output, one line of 3.3 MB, is cut in the kept log. The run of
tree `6662086` above, which holds this change and the new `check.sh`, passed
all six checks, `check-quic.sh` and `check-wire.sh` with the steps of this
change among them.
`evidence/q59.63-controls.log` is each fix of this change undone in turn on
tree `ca88f86`: 18 cases of `quic-self` and 3 runs of `check-quic.sh` and
`check-wire.sh`, each failing at its own step.

2026-11-25 UTC, on morphie, the merged tree: `695ce77` (add-quic-admission
folded on the deep-nesting change, the code of `fd3ff39`) exported to
`~/hom-695ce77` and built from nothing. All six checks exited 0: `check.sh` 84
`ok`, `check-net.sh` 19, `check-quic.sh` 29, `check-wire.sh` 30. Logs
`evidence/q59.63-695ce77-*.log`, exit codes and hashes
`evidence/run-695ce77.txt`; `source.sha256` and `objects.sha256` came out the
same as the two runs above. `reflect-net.elf` is sha256 `1f12c42c…260b64e8`,
the same before and after the checks.

2026-11-25 (UTC) on morphie, Cloud Hypervisor 54.0, tree `73fefe9` exported
with `git archive` to `~/hom-73fefe9-q59.73` (`homoiconic-q59.73`, `q59.64`):
`build.sh examples/factorial.hom`, `build-net.sh`, `check.sh`, `check-net.sh`,
`check-quic.sh` and `check-wire.sh` each exited 0 (`check.sh` 88 lines of
`ok`, `check-wire.sh` 46). Logs `evidence/q59.73-73fefe9-*.log`, exit codes,
times and image hashes in `evidence/q59.73-73fefe9-run.txt`; `reflect.elf`
after the checks is sha256 `37e6d628…e9d5`, `reflect-net.elf` `f009f874…ef5f`;
`source.sha256` and `objects.sha256` are the ones that build wrote, unchanged
from the harden-crossing run of the same tree. New cases: `equal` of data
doubled forty times at the budget 100000000 is the budget line at boot in 11 s
(level 0) and 12 s (level 1) and the reply `81 01` over UDP in 11.5 s; the
largest number 2 MiB holds is `error: unbound` and 5050431 digits at boot in
92 s. The controls, the image with the kernel of `2f1f07a`
(`evidence/q59.73-controls.log`): no power off in 120 s for either `equal`
case, none in 600 s for the number, and `check-net.sh` failing with no reply to
the `equal` request. The time per unit of charge, before and after, is
`evidence/q59.73-measurements.log` and the table in
`openspec/specs/bytecode-machine/spec.md` ("A charge bounds a step's time").
The first attempt, tree `8c31d00`, failed only at `check-wire.sh`'s `worst`
case of the crossing, which `0a5acac` fixed.
