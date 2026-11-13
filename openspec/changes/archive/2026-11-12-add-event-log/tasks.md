# Tasks

- [x] Owner: the user, 2026-11-12. Bead `homoiconic-q59.27`.
- [x] `kernel/Reflect/Log.lean`: `Entry`, `Vm`, `Handle`, `Replay`, `Boot`, `Logged`, `firsts`; the executable `handleRun`, `bootRun`, `vmRun`. Equality of data is decided by a definition written here.
- [x] `kernel/Reflect/LogProof.lean`: determinism, prefix, repeats, restart, the link to the request driver, the machine simulation both ways, soundness of the executable fold.
- [x] `kernel/LogContract.lean`: the statements, for every table, with their axioms.
- [x] `kernel/Surface/Keep.lean`: a session can handle a log (`vmStart`, `vmFrom`) and saves a VM state. Exports `reflect_vm_start`, `reflect_vm_from`.
- [x] `host/session.zig`: the store loop, shared by `keep` and the new `host/vm.zig`.
- [x] `kernel/LogCheck.lean`: the session against the proved fold.
- [x] `examples/ask.log`, `ask-one.log`, `ask-again.log`; the vm scenarios in `host/check.sh`.
- [x] `sh host/check.sh` exits 0.
- [x] Advise by a reader from another model family. Send-back, 2026-11-12, two required fixes: kept states are now checked for their exact shape (a function's environment is not walked, by decision), and the difference between the session's budget and the fold's is stated. Review in `reviews/`.
- [x] Fold. 2026-11-12: `openspec/specs/event-log/spec.md` is new; the ADDED delta is in `openspec/specs/zig-host/spec.md`.
