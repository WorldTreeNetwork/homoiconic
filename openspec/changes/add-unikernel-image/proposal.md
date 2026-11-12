# add-unikernel-image

> **ACTIVE BUILD**

**Rigor:** architecture

Depends on: `add-wire-bytes` (folded, `1379a02`). Spike: `docs/spikes/lean-freestanding/finding.md`, go. Bead: `homoiconic-q59.14`. Authority: the user's intention of 2026-11-10 ("a unikernel that runs in Cloud Hypervisor … run this language"), and on 2026-11-12 the choices "Zig bare metal" for the image and "activate and run" for the set.

## Why

The kernel runs only as a process on someone's operating system. The network the vision describes is made of virtual machines, and a machine that carries a whole operating system to run one evaluator has a great deal in it that nobody proved, nobody needs, and somebody must keep patched. The smallest machine that can run a program is the evaluator and just enough under it to start, get memory, and speak.

## What

- **One image file.** `unikernel/out/reflect.elf` is a static x86_64 ELF file that Cloud Hypervisor starts by direct kernel boot, with no firmware and no operating system inside the guest. It holds the boot code, a Zig layer that stands where an operating system would, the C library, the Lean runtime, and the same compiled Lean objects the host links.
- **It runs one program and stops.** The program's source is put in the image when it is built. On boot the image passes it to `reflect_run`, writes the text that comes back to the serial port, and powers the machine off. The evaluator is the Lean one. Nothing in the image reads the program or looks at the answer.
- **A check that boots it.** `unikernel/check.sh` builds the image, boots it under `cloud-hypervisor`, and compares the serial port's output, byte for byte, for a program with a value, a program that does not finish in its budget, and a program that is not syntax.

## How it is put together

| Part | File | What it does |
|---|---|---|
| Entry | `unikernel/boot.S` | Cloud Hypervisor's PVH entry: 32-bit, paging off. Maps the first 4 GiB one-to-one, enters 64-bit mode, turns on the vector state the processor has, calls `kmain`. Holds the entry for the `syscall` instruction and the fault stubs. |
| Layer | `unikernel/kernel.zig` | Serial port, memory, random bytes, power off, and the system calls the C library and the Lean runtime make. Builds the stack the C library expects and jumps to its start. |
| Program | `unikernel/main.zig` | Initialises the kernel package, calls `reflect_run` on the built-in source, writes the answer. |
| Names | `unikernel/glibc_names.c` | Nine glibc-only names the Lean toolchain's libraries use, in terms of standard functions. |
| Note | `unikernel/onenote.zig` | Run at build time. Leaves one note segment in the ELF file, the one with the PVH entry. |

The C library is not replaced and not rewritten. It is the musl that Zig carries, linked as it is. It reaches the layer with the `syscall` instruction, as it would reach Linux. There is one privilege level, so the instruction jumps to the layer on the caller's stack; the layer steps over the caller's red zone and saves the vector registers.

## Decisions

- **musl, not glibc.** Both ran in the spike. The image is one static file, and glibc's licence puts conditions on distributing that. musl is MIT, comes with Zig, and makes Zig the only compiler and linker beside Lean.
- **Lean's event loop is not started.** A package initialiser calls `initialize_libuv`, which starts a thread. The image has one thread. The build makes that symbol weak in a copy of the runtime archive and `main.zig` defines an empty one. `reflect_run` does no input or output through Lean. A Lean task, or Lean input and output, would fail in this image, and no export uses them.
- **Random bytes come from the processor** (`RDRAND`). If the processor has none the image says so on the serial port and stops. Lean's start-up reads `/dev/urandom`; the layer answers that one path and no other file.
- **A fault is reported, not survived.** A processor fault prints its number, the address and the instruction, then powers off. The page below the stack is not mapped, and the faults that can come from running off the stack are taken on their own stack, so a program that nests too deeply ends with a report and does not write over memory.
- **Memory is the first 4 GiB at most.** That is what the boot code maps. More memory given to the machine is not used.
- **The clock is a stand-in.** The layer answers the time calls from the processor's tick counter at an assumed rate. Nothing a program computes depends on it. A real clock comes with the network, which needs one.
- **The image is built on Linux x86_64.** The Lean toolchain's libraries are per platform, and these are the Linux ones. `host/check.sh` is unchanged and still runs on the Mac. `unikernel/check.sh` needs KVM.
- **`objcopy` is a build dependency**, for the two edits to copies of Lean's archives (the weak symbol, and dropping the list of libraries musl does not have as separate files).

## What is trusted

Everything here is outside the proofs, as the host is. The theorems are about `Reflect`. This change adds to the trusted base: the boot code, the Zig layer (about 500 lines), musl, and Cloud Hypervisor. It removes a guest operating system from it. The Lean compiler, the C compiler and the Lean runtime were trusted already.

## Not in this change

- A network device. `add-unikernel-net`.
- A program given at boot or over the wire. The program is fixed when the image is built.
- More than one thread, interrupts, a timer.
- aarch64.
- Building the image on macOS.
- mjolnir. `mjolnir-unikernel-guest`.

## User journey & surfaces

Command line, on a Linux x86_64 machine with KVM:

```
sh host/check.sh            # compiles the kernel's Lean objects
sh unikernel/build.sh examples/factorial.hom
cloud-hypervisor --kernel unikernel/out/reflect.elf --cpus boot=1 --memory size=512M \
    --serial tty --console off
```

The terminal shows `265252859812191058636308480000000` and the machine powers off.

## Changelog

- 2026-11-12: opened after the spike.
