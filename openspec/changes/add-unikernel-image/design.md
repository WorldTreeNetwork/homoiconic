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

## The build

`unikernel/build.sh <program-file>`:

1. Needs `host/out/lean-*.o`, `runtime.o` and `ffi.o` from `host/check.sh`. It does not compile Lean itself, so the image and the host run the same objects.
2. Copies four of the Lean toolchain's archives and edits the copies with `objcopy`.
3. `zig build-obj` for `kernel.zig` (freestanding) and `main.zig` (musl, with the program embedded).
4. `zig build-exe -target x86_64-linux-musl -static` links everything.
5. `zig run unikernel/onenote.zig` fixes the note segments.

## The check

`unikernel/check.sh` boots three images and compares the whole serial output of each with a file in `unikernel/expected/`:

| Program | Budget | Last lines |
|---|---|---|
| `examples/factorial.hom` | default | the value, `reflect: exit 0` |
| `examples/forever.hom` | 5000 | `no result within 5000 steps`, `reflect: exit 0` |
| a file that is not syntax | default | the reader's error text, `reflect: exit 0` |

A fourth image is built from a layer with one system call removed from its table, to show the check fails on `is not provided`. Each boot has a 60 second limit, and reaching it is a failure. Cloud Hypervisor's own exit status must be 0.

The budget is a second argument to `build.sh` and is fixed in the image with the program.

## Unverified hypotheses

- ch-54: claim: the image boots the same way on Cloud Hypervisor 54.0, the version mjolnir pins. confidence: high. verification: none. synthesis path: this change's check, run with a 54.0 binary.
