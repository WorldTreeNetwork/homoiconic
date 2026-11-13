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
The image has no network interface yet.

`build.sh` runs Lake, compiles generated C for Surface.Host's local imports,
and links identical Lean objects into `out/reflect.elf` and
`out/reflect-linux`. It does not use host/check.sh or host/out artifacts.
`versions.txt`, `source.sha256` and `objects.sha256` record provenance.
Source/toolchain or object changes reject reuse: remove `unikernel/out`
and rebuild. Build outputs are ignored. Checks start from an empty output
folder and compare full serial streams against the Linux executable and
independent expected values, including a rendering larger than 64 KiB.

## Runtime audit (Lean v4.35.0)

The permitted entry is `main.zig` -> module initializer ->
`kernel_finish_initialization` in `host/runtime.c` -> `reflect_run` in
`kernel/Surface/Host.lean`. That export copies input bytes, calls
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
