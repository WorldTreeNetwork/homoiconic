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

## Owed from 2026-11-12 advise — astra-arch-review

- [ ] R1: Reconcile the Linux build prerequisite and host oracle with the known `host/check.sh` link failure; name the successful path/dependency and require clean, pinned, provenance-checked objects with fail-fast artifact checks. See `reviews/2026-11-12-advise.md`.
- [ ] R2: Bound the stack-safety guarantee, including guard exclusion/alignment, frame growth and syscall headroom; require a deterministic guard/IST fault check with address and adjacent-memory integrity assertions, separate from a runtime stack message.
- [ ] R3: Pin the syscall ABI and CPU/XSAVE feature policy, enabled state and save-area requirements; add register/vector/red-zone preservation and unsupported-feature scenarios.
- [ ] R4: Specify complete output using the `reflect_run` length/capacity contract and explicit infrastructure failures; add a byte-exact answer larger than the initial buffer.
- [ ] R5: Specify RDRAND carry-flag handling, bounded retries and exhaustion; add absent/failing-random scenarios and named evidence for one thread, the no-op libuv link, the permitted runtime path and clock independence.
- [ ] R6: Scope the no-reader/no-evaluator rule to non-Lean image code and add source/link inspection of Lean ownership and the shared object path.
