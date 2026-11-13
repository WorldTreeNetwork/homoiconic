# Design

## The boundary

```
 Cloud Hypervisor
   │ PVH entry (32-bit, %ebx = start info)
 boot.S ── 64-bit, 4 GiB mapped ──► kmain (kernel.zig)
                                      │ builds argc/argv/auxv, jumps
                                    musl _start ► main (main.zig)
                                      │                 │ reflect_run(source, budget)
                                      │               Lean: read, compile, run, render
                                      │ syscall
                                    syscall_dispatch (kernel.zig) ► serial, memory, power
```

Zig is on both sides of the C library: `kernel.zig` under it, `main.zig` over it. The two do not call each other. `main.zig` is ordinary code that writes to file 1; `kernel.zig` is what makes file 1 the serial port.

## The system calls

Answered with an effect: `write` and `writev` to files 1 and 2 (the serial port), `brk`, `mmap` and `munmap` of anonymous memory, `arch_prctl` (set the thread pointer), `getrandom`, `open`/`read`/`close` of `/dev/urandom`, `exit` and `exit_group` (power off), and `kill`/`tgkill` (an abort: say so and power off).

Answered with a fixed value: `mprotect`, `madvise`, signal set-up, `set_tid_address`, `getpid`, `gettid`, `prlimit64` (the stack's size), `sysinfo` (memory totals), the clock calls, `sched_getaffinity` (one processor), `futex` (nothing waits; a wait returns at once).

Every other number prints `reflect: system call N is not provided` and returns "not implemented". The check fails if that line appears, so a new dependency of the runtime is seen when it arrives.

## Memory

Start info gives the memory map. The layer takes the region that holds the image, up to 4 GiB. From the top: the stack (16 MiB) with an unmapped 2 MiB page under it. From the image's end: the `brk` area (a quarter of what is left), then the `mmap` area. Freed ranges are kept sorted and merged with their neighbours; memory handed out again is zeroed first; memory never handed out is already zero.

## Faults

The boot code loads a task segment with one alternate stack. Double fault, stack fault and page fault use it. Every fault ends in `fault_report` and power off. There is no return from a fault.

## Stack and CPU contract

The guard is a 2 MiB aligned, unmapped 2 MiB page below a 16 MiB stack. Both allocators end below the guard. Page, stack and double faults use a separate 64 KiB IST stack. The supported claim is contiguous growth touching the guard; arbitrary unchecked dynamic frames that skip 2 MiB are outside this guarantee. Neither prebuilt Lean/C archives nor arbitrary native code are claimed to have stack-clash protection. Syscall entry consumes 128 red-zone bytes, 88 bytes of saved registers, a 4096-byte XSAVE reserve and up to 63 alignment bytes before calling the bounded, nonrecursive dispatcher. This overhead also lies within the guard's width. The linked path and deep-source check establish the supported workload, not a proof for all native stack accesses.

The CPU floor is x86_64 with XSAVE and RDRAND. Missing features are diagnosed before entering musl. XCR0 enables only x87/SSE (mask 3) and AVX when available (mask 7); CPUID leaf 0xD must report a save area no larger than the 4096-byte reservation. XSAVE/XRSTOR addresses are 64-byte aligned; dispatch calls have 16-byte stack alignment. Syscall returns preserve general registers except RAX (result), RCX (return address), R11 (saved flags), and restore flags, x87, MXCSR and enabled vector registers. The caller's 128-byte red zone is untouched.

## The build

Linux x86_64, Lean 4.35.0 (`kernel/lean-toolchain`), Zig 0.16.0 and its musl 1.2.5, GNU objcopy, sha256sum. The supported hypervisor is Cloud Hypervisor 54.0, KVM, one vCPU, 512 MiB.

`unikernel/build.sh <program-file> [step-budget]` runs Lake and compiles generated C for Surface.Host's transitive local imports, plus ffi.c and host/runtime.c. It does not depend on the failing Linux host/check.sh link. The image and `out/reflect-linux` link the identical generated Lean objects and copied runtime archives, recorded with versions and hashes. Reuse requires matching source/toolchain provenance and object hashes; missing, changed or wrong-platform artifacts fail. The check starts with no output directory.

The build weakens initialize_libuv in a runtime archive copy and drops .deplibs sections from copies of the three C++ archives. Zig links a static musl ELF with the PVH note, and a Linux process without the boot code and syscall layer. No ELF note rewrite is needed with this link.

## Output and runtime path

main.zig calls only module initialization, kernel_finish_initialization and reflect_run. The export copies bytes, calls Surface.runText (reader, compile, bounded machine, renderer), and copies the result back. No task or async IO lies on that path. Lean runtime initialization still runs; only initialize_libuv is replaced, skipping loop facilities as well as its worker. See `unikernel/README.md` for the pinned source audit. Re-audit on toolchain or imports changing. No claim covers other exports or arbitrary Lean IO.

A 65536-byte first buffer is retried with the length reflect_run returns; allocation, initialization and write failures produce a nonzero process exit. Nothing in the host inspects the returned language text. Kernel outcomes, including syntax errors, finish with exit 0.

RDRAND accepts only results whose carry flag reports success, retries at most ten times, and diagnoses exhaustion then powers off. AT_RANDOM, getrandom and /dev/urandom share this path. There is no clock fallback. Reported time is a tick-counter stand-in and does not determine a language result.

## The check

Clean build and byte-exact comparison against the Linux process for factorial, budget exhaustion, malformed syntax, embedded zero bytes and a 128894-byte array rendering. Each boot must power off with hypervisor status 0 within 60 seconds. A stopped clock must preserve the factorial answer. Source inspection establishes the Lean semantic boundary; nm checks main's export references and that initialize_libuv resolves to main's empty function. Compiled object/archive hashes are checked.

Negative and hardware probes: omit a startup syscall and require its number in the diagnostic; nest source deeply and require a stack fault; write into the unmapped guard and require fault 14 at that address, the IST-stack marker and an intact adjacent sentinel. Preserve general registers, flags, red-zone sentinels, x87/MXCSR and all enabled vector registers across a handler that clobbers state. Controlled absent XSAVE/RDRAND and random-failure builds must terminate with the exact diagnostic. Random interfaces must serve requests on the positive path. Removing vector restore and red-zone skipping must make the preservation probe fail.
