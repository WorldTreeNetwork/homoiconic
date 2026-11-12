---
spike_id: lean-freestanding
hypothesis_id: lean-freestanding
source_synthesis: null
run_at: 2026-11-12T02:20:00-08:00
time_spent_min: 50
verdict: go
version-pinned: lean 4.35.0, zig 0.16.0, cloud-hypervisor 53.0, gcc 16.2.1 with static glibc, linux 7.2.6 (KVM host)
---

# Spike: the Lean runtime in an image with no operating system

## Claim Tested

The Lean 4.35 runtime, with the kernel's compiled modules, links and initialises in a freestanding Zig image with a small libc shim and no threads, and Cloud Hypervisor boots that image directly.

## Minimal Test

One static ELF file holds everything: boot code, a Zig layer that stands where an operating system would, an unmodified static C library, the Lean runtime, and the kernel's Lean objects from `host/out`.

- `src/boot.S`: the PVH entry Cloud Hypervisor jumps to (32-bit, paging off). It maps the first 4 GiB one-to-one, enters 64-bit mode, turns on SSE and AVX state, and calls `kmain`. It also holds the entry for the `syscall` instruction and the fault stubs.
- `src/kernel.zig`: serial port, a page allocator, and the system calls the C library and the Lean runtime make. It builds the stack the C library expects and jumps to its `_start`. It does not evaluate.
- `src/main.zig`: the program. It initialises the kernel package, passes `examples/factorial.hom` to `reflect_run`, and writes the text that comes back.
- `src/onenote.py`: turns the ELF file's other note segments into empty ones (see below).

The image was booted with `cloud-hypervisor --kernel out/reflect.elf --cpus boot=1 --memory size=512M --serial file=out/serial.log --console off`.

## Evidence

`evidence.log`, from `repro-command.sh` on an x86_64 KVM machine:

```
exit 0 after 65 ms
reflect: booted
reflect: memory to 0x0000000020000000
reflect: starting
265252859812191058636308480000000
reflect: exit 0
```

The value is the one `host/check.sh` expects for `examples/factorial.hom`. The 65 ms is the whole `cloud-hypervisor` process, from start to exit. The image file is 5.8 MB.

## Verdict: go, with the claim corrected

The Lean runtime runs with no operating system under it. It did not take a libc shim. An unmodified static C library runs as it is, and the Zig layer answers its system calls. That is less code to write and to trust than a replacement C library.

What it took, each found by running:

- **The system calls are few.** Used on this path: `write`, `brk`, `mmap`, `munmap`, `mprotect`, `arch_prctl`, `set_tid_address`, `set_robust_list`, `rseq`, `prlimit64`, `getrandom`, `sysinfo`, `clock_getres`, `openat`, `read`, `close`, `exit_group`. `syscall` works with one privilege level: it jumps to the handler on the caller's stack. The handler steps over the caller's red zone and saves the vector registers.
- **Lean's start-up creates a thread.** A package initialiser calls `initialize_libuv`, which starts an event-loop thread. The link sends that call to an empty function (`--wrap=initialize_libuv`). `reflect_run` does no input or output through Lean, so nothing misses the loop.
- **Lean's start-up reads `/dev/urandom`.** The layer answers that one path.
- **Cloud Hypervisor's loader keeps the last note segment's answer.** A static link has three note segments and the PVH entry is in the first, so the loader reported no PVH header. With the other two made empty the image boots.
- **The processor state has to be turned on before the C library starts.** The C library picks AVX routines when the processor reports them usable.

## Not shown

- Cloud Hypervisor 54.0, the version mjolnir pins. This ran on 53.0.
- Any device but the serial port. No interrupts, no timer, no network.
- More than one thread. Lean tasks and Lean input and output would fail.
- A real random source and a calibrated clock. Both are stand-ins here.
- Memory handed back well: freed ranges are reused first-fit and never merged.
- musl in place of glibc. glibc is LGPL, which matters if the image is distributed as one static file. The Lean toolchain's libraries were built against glibc.
- That `host/check.sh` passes on Linux. Its last link fails there (`_start` defined twice: Zig's and the C library's). Tracked separately.
