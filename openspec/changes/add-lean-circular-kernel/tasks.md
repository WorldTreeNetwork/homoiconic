# Tasks

- [x] Add a Lean 4 package whose `lake build` succeeds
- [x] Define terms with variable, abstraction, application, and quote
- [ ] Prove the metacircular equality for the pure fragment, and not for quoted re-entry

## Owed from advise — 2026-11-08, astra-arch-review

- [x] R1: Specify the object-language interpreter term/construction, program encoding, and execution route through the Lean evaluator; reconcile the quoted interpreter with the evaluator's domain without replacing interpretation with a host-eval shortcut. See reviews/2026-11-08-advise.md.
- [x] R2: State the proposed theorem signature and evaluator domain/codomain, including evaluation strategy, environments/open terms, divergence or fuel, and interpreter/direct-result correspondence; reconcile any premises with the promised all-quote-free fragment. See reviews/2026-11-08-advise.md.
- [x] Add acceptance checks for the theorem's actual type and axiom dependencies (no sorry/admit or newly assumed correctness/semantic axioms), a nontrivial pure application through both routes, the selected divergence/open-term behavior, and exclusion of quoted inputs from the theorem premise.
- [x] Obtain fresh advise from astra-arch-review after the R1/R2 contract and verification requirements are reconciled.
- [x] Fresh advise after preparation

## Owed from fresh advise — 2026-11-08, astra-arch-review

- [x] R3: Reconcile application and open-variable acceptance examples with encoded interpreter outcomes: direct outcome `o`, interpreter outcome `w`, and `Represents o w`; do not require identical raw outcomes. See reviews/2026-11-08-advise-2.md.
- [x] R4: Specify function-position unbound-error propagation in Direct and the interpreter, narrow the blanket open-term claim, and require checks for an unbound function with a diverging argument and for an open lambda returning a closure. See reviews/2026-11-08-advise-2.md.
- [x] R5: Require proved coverage of every interpreter outcome on pure inputs, or equivalent strengthened correctness, so divergence rules out all interpreter derivations rather than only represented outcomes; reconcile the omega check. See reviews/2026-11-08-advise-2.md.
- [x] R6: Require an executable Lean evaluation entry with explicit nontermination/bounds behavior, proved correspondence to the theorem's evaluation relation, and execution checks for the application and open-variable examples; keep Zig/ABI work out of scope. See reviews/2026-11-08-advise-2.md.
