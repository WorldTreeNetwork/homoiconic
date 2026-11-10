# language-partition

At fold, the overview's last sentence becomes: "The interpreter theorem is in `openspec/specs/code-as-data/spec.md`."

## MODIFIED Requirements

### Requirement: Circularity is metacircular
<!-- base: 132e1ac05d6a780c3a52b34d37a5392207658e42 openspec/specs/language-partition/spec.md -->

The kernel SHALL prove that evaluating an interpreter written as a term of the language on a program equals evaluating that program directly. The statement SHALL cover every program of the language, not a fragment. The theorem and its exact statement are in `openspec/specs/code-as-data/spec.md`.

#### Scenario: The interpreter theorem is the kernel's

- GIVEN this partition
- WHEN someone asks what makes the language circular
- THEN the answer is the theorem `reflective`, proved in Lean about the evaluator that runs
