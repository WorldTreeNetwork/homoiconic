# Tasks

- [x] Owner: go from the user, 2026-11-11. Bead `homoiconic-q59.18`.
- [x] `Reflect/Store.lean`: pieces, the store, `Unf`, partial states, `lstep` and `lrun` with a pause, `RState`.
- [x] `Reflect/StoreProof.lean`: saving loses nothing; the lazy machine reaches every plain state; a missing piece is a pause; more pieces change nothing; stores that agree give the same result; a program through the store has its direct outcome.
- [x] A turn of the request driver from a stored continuation agrees with the machine.
- [x] `kernel/StoreContract.lean`: fourteen statements for every operation table and every kind of reference, no table imported, axioms printed.
- [x] `kernel/StoreCheck.lean`: eight programs stopped at four points, cut at every value, run whole and with a piece withheld then supplied; a waiting run kept and continued.
- [x] `lake build`, the contracts, the checks and `sh host/check.sh` exit 0.
- [ ] Advise by a reader from another model family.
- [ ] Fold: add `state-store`; amend `ARCHITECTURE.md`, `kernel/README.md` and `docs/PROOFS.md`; note the state half of stage 5 in the vision.
