# Tasks

- [x] Owner: roadmap node `homoiconic-q59.14`; the user's "Zig bare metal" and "activate and run", 2026-11-12.
- [x] Spike `lean-freestanding`: go.
- [ ] Advise by a reader from another model family.
- [ ] `unikernel/boot.S`: PVH entry, 64-bit mode, the task segment and alternate stack, the unmapped page under the stack, `syscall` entry, fault stubs.
- [ ] `unikernel/kernel.zig`: serial, merged free ranges, `RDRAND`, the system call table, fault report, power off.
- [ ] `unikernel/main.zig`, `unikernel/glibc_names.c`, `unikernel/onenote.zig`.
- [ ] `unikernel/build.sh <program-file> [step-budget]`.
- [ ] `unikernel/check.sh` and `unikernel/expected/`: the three programs, the missing system call, the time limit.
- [ ] The check passes on Cloud Hypervisor 54.0.
- [ ] A program that nests too deeply ends in a fault report.
- [ ] `unikernel/README.md`.
- [ ] Fold: add `unikernel-image`; amend `ARCHITECTURE.md`; record what is trusted in `docs/PROOFS.md`.
