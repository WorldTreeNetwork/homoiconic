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

The command line is `[step-budget [levels]]`, at most 1023 bytes; a longer one
stops the image with a line instead of being cut. The budget is a whole number
below 2^64 and defaults to the one built in. The levels are a whole number from
0 to 8 and default to 1: the bytes run through `reflect_interp`, the
interpreter written in the language, on the machine. Level 0 runs the program
itself; level 2 runs the interpreter in the interpreter. The kernel builds the
tower before the budget counts a step, so the levels are bounded by the
kernel (`Surface.maxLevels`, which `main.zig` asks for by `reflect_max_levels`),
not by the budget. A word that is not a number, and a number past these
limits, each end in a line of their own and `reflect: exit 2`. With no
`--initramfs` the image runs the source built into it through `reflect_run`.

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
| literal nested arrays | full stack | full stack (from 262144 deep; 131072 answers) |
| one number of 2 MiB (tag 2) | | no answer in 300 s, 12 MiB |

At 16 MiB one array of zeros ran out of memory as data. 2 MiB is the largest
power of two at which every shape here gave its answer or the kernel's text.
Two limits are not the byte limit's. A literal nested deeper than the stack
holds ends in the report of a full stack, as a deep source does. A number of
megabytes is read (`takeBE`) and printed in time that grows with the square of
its length: one of 128 KiB took 393 s as a Linux process, so one near the
limit never finishes inside any check's time (`homoiconic-q59.64`).

The limit bounds what the bytes cost, not what a run costs. A run's memory
grows with its steps: `examples/forever.hom`, 52 bytes, ran the image out of
memory at the default budget of 100000000 steps at levels 0 and 1 (1151 MiB
at level 0 as a Linux process, about 4.6 bytes a step at level 1), and the
list of zeros above, at 1 MiB through one interpreter, did after a few seconds
of steps. No byte limit prevents that; a budget is what bounds it
(`homoiconic-q59.65`). The network image takes at most 1176 program bytes (a
1200-byte frame less its 24-byte header) and a budget of at most 100000000
steps, so what its bytes cost is small, and its runs have the same per-step
growth.

`build.sh` runs Lake, compiles generated C for Surface.Host's local imports,
and links identical Lean objects into `out/reflect.elf` and
`out/reflect-linux`: exactly the objects `objects.sha256` names, not whatever
lies in `out/lean`. It does not use host/check.sh or host/out artifacts.
`versions.txt`, `source.sha256` and `objects.sha256` record provenance.
Source/toolchain or object changes reject reuse: remove `unikernel/out`
and rebuild. Build outputs are ignored. Checks start from an empty output
folder and compare full serial streams against the Linux executable and
independent expected values, including a rendering larger than 64 KiB.

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
below it. A separate deeply nested source must fault on the alternate stack.
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
