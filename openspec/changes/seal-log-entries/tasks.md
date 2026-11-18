# Tasks

- [x] Owner: the user, 2026-11-17. Bead `homoiconic-q59.28`.
- [x] `kernel/Reflect/Log.lean`: `Entry.seal`, `Entry.Sealed`. `kernel/Reflect/Node.lean`: `Op.seal`, `Op.Sealed`.
- [x] `kernel/Reflect/LogProof.lean`: `sealed_same`, `firsts_sub`, `firsts_has`, `sealed_first`. `kernel/Reflect/NodeProof.lean`: the same for ops.
- [x] `kernel/LogContract.lean`, `kernel/NodeContract.lean`: the statements, with their axioms.
- [x] `kernel/Surface/Keep.lean`: `entryName`; `dataEntries` and `dataOps` seal what they read; a refused op is reported by its place.
- [x] `kernel/LogCheck.lean`, `kernel/NodeCheck.lean`: the proved runs are given the seals the session makes; two answers under one mark; the name is the hash.
- [x] `host/check.sh`, `examples/ask-again.log`: the scenarios.
- [x] `sh host/check.sh` exits 0.
- [ ] Advise by a reader from another model family.
- [ ] Fold.
