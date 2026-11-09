## ADDED Requirements

### Requirement: The kernel is executable Lean

The system SHALL implement the circular evaluator as a Lean 4 package. `lake build` SHALL succeed for that package.

#### Scenario: The package builds

- GIVEN the kernel package
- WHEN `lake build` runs
- THEN the build exits 0

### Requirement: Terms include quote

The kernel SHALL represent variables, abstractions, applications, and quotes of terms. Quoting a term SHALL build a term and SHALL NOT evaluate the quoted term.

#### Scenario: Quote is data

- GIVEN a term
- WHEN it is quoted
- THEN the quote is a term and is not evaluated by that construction

### Requirement: The pure fragment is metacircular

The pure fragment SHALL be the terms that contain no quote, including open terms and terms that diverge. For every such program `p` and every pure outcome `o`, the kernel SHALL prove `Direct [] p o` if and only if `app interpreterBody (encode p)` derives some `w` at the empty environment and `Represents o w`.

`Direct` SHALL be call-by-value, function before argument, over de Bruijn terms. A pure outcome SHALL be a closure or `unbound i`. An index past the environment SHALL derive `unbound i`. Divergence SHALL be the absence of a derivation. The theorem SHALL have no fuel argument.

`encode` SHALL be the Mogensen–Scott encoding of pure terms, using Church numerals for indices. `interpreterBody` SHALL be one closed pure term whose three continuations implement variable lookup, abstraction, and application. It SHALL NOT call `Direct` or `Eval`. The interpreter-term SHALL be `quote interpreterBody`. The execution route SHALL project that payload and evaluate `app interpreterBody (encode p)` with `Direct`. That projection SHALL NOT be a call to `Direct` on the quoted body.

The theorem SHALL NOT claim this equality for a program that contains a quote. The quote rule SHALL return its payload as data and SHALL NOT be used on the input program.

#### Scenario: Pure program

- GIVEN `app (lam (var 0)) (lam (var 0))`
- WHEN both routes are derived at the empty environment
- THEN each outcome is `closure (var 0) []` and `Represents` relates them

#### Scenario: An open term is unbound

- GIVEN `var 0` and the empty environment
- WHEN the term is evaluated directly and through the interpreter
- THEN both routes derive `unbound 0`

#### Scenario: A diverging term has no derivation

- GIVEN `app (lam (app (var 0) (var 0))) (lam (app (var 0) (var 0)))`
- WHEN a derivation at the empty environment is sought
- THEN neither route derives an outcome

#### Scenario: Quoted re-entry is outside the theorem

- GIVEN `quote (var 0)`
- WHEN someone asks whether the metacircular theorem covers it
- THEN `Pure` does not hold, and the theorem does not

### Requirement: The theorem's dependencies are the logic, not an assumption of correctness

`metacircular` SHALL be a Lean declaration. Its axiom dependencies SHALL NOT include `sorryAx` and SHALL NOT include an axiom declared by this package. `Direct` SHALL be proved deterministic.

#### Scenario: No admitted correctness

- GIVEN the compiled theorem `metacircular`
- WHEN its axiom dependencies are printed
- THEN `sorryAx` is absent and no axiom from this package is present
