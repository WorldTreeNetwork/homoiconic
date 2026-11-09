## ADDED Requirements

### Requirement: The kernel is executable Lean

The system SHALL implement the circular evaluator as a Lean 4 package. `lake build` SHALL succeed for that package.

#### Scenario: The package builds

- GIVEN the kernel package
- WHEN `lake build` runs
- THEN the build exits 0

### Requirement: Terms include quote

The kernel SHALL represent variables, abstractions, applications, and quotes of terms.

#### Scenario: Quote is data

- GIVEN a term
- WHEN it is quoted
- THEN the quote is a term and is not evaluated by that construction

### Requirement: The pure fragment is metacircular

For every program in the pure fragment, the kernel SHALL prove that evaluating the interpreter-term on that program equals evaluating the program directly. The pure fragment SHALL be the terms that contain no quote. The theorem SHALL NOT claim that equality for a program that contains a quote.

#### Scenario: Pure program

- GIVEN a program with no quote
- WHEN the interpreter-term is evaluated on it
- THEN the result equals direct evaluation of that program

#### Scenario: Quoted re-entry is outside the theorem

- GIVEN a program that contains a quote
- WHEN someone asks whether the metacircular theorem covers it
- THEN the theorem does not
