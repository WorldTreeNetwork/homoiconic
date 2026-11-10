# Tasks

- [x] Owner: `go` from the user, 2026-11-10. Bead `homoiconic-q59.11`.
- [x] `Reflect/Request.lean`: `askTerm`, `payloadTerm`, `resumeTerm`, `Sys`, `Ending`, `Drive`, the three ways of evaluating, `Interact`, `InteractI`, `InteractM`, `driveRun`, `converse`.
- [x] `Reflect/RequestProof.lean`: determinism, resume, extra answers, turn-by-turn agreement lifted to runs, the interpreter and machine instances, soundness of `converse`.
- [x] `kernel/RequestContract.lean`: nine statements as `∀ [Ops], …`, with no table imported; axioms printed.
- [x] The reader resolves `ask`; a program's own binding of the name wins.
- [x] `Surface.converseText` and twenty-two examples in `Surface.converses`, run by `Surface/Check.lean`.
- [x] Export `reflect_converse`; command `host/out/ask`; five command checks and six refusals in `host/check.sh`.
- [x] `lake build`, three contracts, `ReflectRun.lean`, `Surface/Check.lean` and `sh host/check.sh` exit 0.
- [x] Advise by a reader from another model family. Send-back, 2026-11-10, two required fixes to the description and three notes, all answered; no proof finding. Review in `reviews/`.
- [ ] Fold: add `requests`, apply the deltas to `surface-syntax` and `zig-host`, amend `ARCHITECTURE.md`, the READMEs and `docs/PROOFS.md`, and note P10, P11 and P12 in the vision.
