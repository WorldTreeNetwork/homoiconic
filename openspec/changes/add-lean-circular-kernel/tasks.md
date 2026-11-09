# Tasks

- [ ] Add a Lean 4 package whose `lake build` succeeds
- [ ] Define terms with variable, abstraction, application, and quote
- [ ] Prove the metacircular equality for the pure fragment, and not for quoted re-entry

## Owed from advise — 2026-11-08, astra-arch-review

- [ ] R1: Specify the object-language interpreter term/construction, program encoding, and execution route through the Lean evaluator; reconcile the quoted interpreter with the evaluator's domain without replacing interpretation with a host-eval shortcut. See reviews/2026-11-08-advise.md.
- [ ] R2: State the proposed theorem signature and evaluator domain/codomain, including evaluation strategy, environments/open terms, divergence or fuel, and interpreter/direct-result correspondence; reconcile any premises with the promised all-quote-free fragment. See reviews/2026-11-08-advise.md.
- [ ] Add acceptance checks for the theorem's actual type and axiom dependencies (no sorry/admit or newly assumed correctness/semantic axioms), a nontrivial pure application through both routes, the selected divergence/open-term behavior, and exclusion of quoted inputs from the theorem premise.
- [ ] Obtain fresh advise from astra-arch-review after the R1/R2 contract and verification requirements are reconciled.
