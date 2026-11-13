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
- [ ] Advise by a reader from another model family.
- [ ] Fold.
