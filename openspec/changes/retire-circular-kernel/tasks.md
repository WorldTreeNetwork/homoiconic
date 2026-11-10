# Tasks

- [x] Owner: the user approved deleting the first kernel, 2026-11-10.
- [x] Delete `kernel/Circular/`, `kernel/Circular.lean`, `kernel/Contract.lean`, `kernel/Run.lean`, `kernel/Axioms.lean`, and the `Circular` library in `kernel/lakefile.toml`.
- [x] Remove `kernel_run`, its initializer and its cases from `host/check.zig`. Keep one check that bytes past the declared length are not read, now through `reflect_run`.
- [x] `host/run.zig`: read a file, call `reflect_run`, print the bytes. Zig does not read the program or the answer.
- [x] `host/check.sh` builds `out/check` and `out/run`, checks both `Reflect` contracts, and runs the command on `examples/` and on two refusals.
- [x] Compile the host's Lean objects with `-O3`, assertions left on.
- [x] Rewrite `kernel/README.md` and `host/README.md` for one evaluator.
- [x] `lake build`, `Surface/Check.lean`, `ReflectContract.lean`, `MachineContract.lean`, `ReflectRun.lean` and `sh host/check.sh` exit 0.
- [x] After review: an embedded zero byte is checked through `reflect_run`; wrong arguments print one line; a failed write exits 2 with a line; `check.sh` asserts exit status, empty output and one error line for five refusals, with no pipeline in a condition; stale text outside the first fold list is claimed in the proposal.
- [ ] Advise by a reader from another model family.
- [ ] Fold: remove `openspec/specs/lean-kernel/`, apply the deltas, amend `ARCHITECTURE.md` and the two overview paragraphs named in the proposal.
- [ ] Close `homoiconic-3gx` and `homoiconic-q59.5`.
