# Tasks

- [ ] Owner: go from the user. Bead `homoiconic-q59.18`.
- [ ] `Reflect/Store.lean`: references as a parameter, partial data, partial values, partial states, the store, `Resolves`, saving, the lazy step and run with a `needs` stop.
- [ ] `Reflect/StoreProof.lean`: saving loses nothing; the lazy machine simulates the plain one; missing is a pause; adding pieces changes no result; stores that agree give the same results.
- [ ] The request driver over stored state: end a run with a root, continue from a root; lift `interact_resume`.
- [ ] `kernel/StoreContract.lean`: the statements as `∀ [Ops], …` for every kind of reference, no table imported, axioms printed.
- [ ] An executable store in memory and a check: every example cut at every value, run whole and run with pieces withheld then supplied.
- [ ] `lake build`, the contracts, `Surface/Check.lean` and `sh host/check.sh` exit 0.
- [ ] Advise by a reader from another model family.
- [ ] Fold: add `state-store`; amend `ARCHITECTURE.md`, `kernel/README.md` and `docs/PROOFS.md`; note the state half of stage 5 in the vision.
