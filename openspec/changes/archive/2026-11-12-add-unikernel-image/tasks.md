# Tasks

- [x] Owner: roadmap node `homoiconic-q59.14`; the user's "Zig bare metal" and "activate and run", 2026-11-12.
- [x] Spike `lean-freestanding`: go.
- [x] Advise by a reader from another model family.
- [x] `unikernel/boot.S`: PVH entry, 64-bit mode, the task segment and alternate stack, the unmapped page under the stack, `syscall` entry, fault stubs.
- [x] `unikernel/kernel.zig`: serial, merged free ranges, `RDRAND`, the system call table, fault report, power off.
- [x] `unikernel/main.zig`, `unikernel/glibc_names.c`; PVH note linked directly without rewriting.
- [x] `unikernel/build.sh <program-file> [step-budget]`.
- [x] `unikernel/check.sh` and `unikernel/expected/`: program comparisons, guard/state/random probes, the missing system call and the time limit.
- [x] The check passes on Cloud Hypervisor 54.0.
- [x] A program that nests too deeply ends in a fault report.
- [x] `unikernel/README.md`.
- [x] Fold: add `unikernel-image`; amend `ARCHITECTURE.md`; record what is trusted in `docs/PROOFS.md`.

## Owed from 2026-11-12 advise — astra-arch-review

- [x] R1: Reconcile the Linux build prerequisite and host oracle with the known `host/check.sh` link failure; name the successful path/dependency and require clean, pinned, provenance-checked objects with fail-fast artifact checks. See `reviews/2026-11-12-advise.md`.
- [x] R2: Bound the stack-safety guarantee, including guard exclusion/alignment, frame growth and syscall headroom; require a deterministic guard/IST fault check with address and adjacent-memory integrity assertions, separate from a runtime stack message.
- [x] R3: Pin the syscall ABI and CPU/XSAVE feature policy, enabled state and save-area requirements; add register/vector/red-zone preservation and unsupported-feature scenarios.
- [x] R4: Specify complete output using the `reflect_run` length/capacity contract and explicit infrastructure failures; add a byte-exact answer larger than the initial buffer.
- [x] R5: Specify RDRAND carry-flag handling, bounded retries and exhaustion; add absent/failing-random scenarios and named evidence for one thread, the no-op libuv link, the permitted runtime path and clock independence.
- [x] R6: Scope the no-reader/no-evaluator rule to non-Lean image code and add source/link inspection of Lean ownership and the shared object path.
