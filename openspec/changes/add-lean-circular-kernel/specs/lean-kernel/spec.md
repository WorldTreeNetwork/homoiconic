## ADDED Requirements

### Requirement: The kernel is executable Lean

The system SHALL implement the circular evaluator as a Lean 4 package. `lake build` SHALL succeed for that package. The package SHALL define `evalFuel`, a total Lean function from fuel, an environment, and a term to `Option` of a pure outcome. `some o` SHALL imply `Direct`. A `Direct` derivation SHALL be returned at some fuel. On `omega` at the empty environment, every fuel SHALL return `none`. The identity application and the open variable SHALL be run through `evalFuel` on the direct term and on the interpreter application. Those two runs SHALL NOT be required to use the same fuel. This entry SHALL NOT call Zig.

#### Scenario: The package builds

- GIVEN the kernel package
- WHEN `lake build` runs
- THEN the build exits 0

#### Scenario: The executable entry matches the relation

- GIVEN `app (lam (var 0)) (lam (var 0))` and `var 0` at the empty environment
- WHEN `evalFuel` runs the direct term and the interpreter application
- THEN the direct run returns the `Direct` outcome, and the interpreter run returns a `w` that `Represents` relates to that outcome

### Requirement: Terms include quote

The kernel SHALL represent variables, abstractions, applications, and quotes of terms. Quoting a term SHALL build a term and SHALL NOT evaluate the quoted term.

#### Scenario: Quote is data

- GIVEN a term
- WHEN it is quoted
- THEN the quote is a term and is not evaluated by that construction

### Requirement: The pure fragment is metacircular

The pure fragment SHALL be the terms that contain no quote, including terms with free indices and terms that diverge. For every such program `p` and every pure outcome `o`, the kernel SHALL prove `Direct [] p o` if and only if `app interpreterBody (encode p)` derives some `w` at the empty environment and `Represents o w`.

The kernel SHALL also prove `coverage`: every `w` derived by that interpreter route represents some source outcome. For a pure term with no `Direct` outcome, the interpreter route SHALL have no derivation.

`Direct` SHALL be call-by-value, function before argument, over de Bruijn terms. A pure outcome SHALL be a closure or `unbound i`. An index past the environment SHALL derive `unbound i`. If the function of an application derives `unbound i`, the application SHALL derive `unbound i` and SHALL NOT evaluate the argument. A lambda SHALL derive a closure and SHALL NOT evaluate its body. Divergence SHALL be the absence of a derivation. The theorem SHALL have no fuel argument.

`encode` SHALL be the Mogensen–Scott encoding of pure terms, using Church numerals for indices. `interpreterBody` SHALL be one closed pure term whose three continuations implement variable lookup, abstraction, and application. It SHALL NOT call `Direct` or `Eval`. The interpreter-term SHALL be `quote interpreterBody`. The execution route SHALL project that payload and evaluate `app interpreterBody (encode p)` with `Direct`. That projection SHALL NOT be a call to `Direct` on the quoted body.

The theorem SHALL NOT claim this equality for a program that contains a quote. The quote rule SHALL return its payload as data and SHALL NOT be used on the input program.

#### Scenario: Pure program

- GIVEN `app (lam (var 0)) (lam (var 0))`
- WHEN both routes are derived at the empty environment
- THEN the direct route derives `closure (var 0) []`, the interpreter route derives a different `w`, and `Represents` relates that closure to `w`

#### Scenario: An open variable is unbound

- GIVEN `var 0` and the empty environment
- WHEN the term is evaluated directly and through the interpreter
- THEN the direct route derives `unbound 0`, and the interpreter route derives a different closure `w` such that `Represents (unbound 0) w`

#### Scenario: An unbound function skips a diverging argument

- GIVEN `app (var 0) omega` at the empty environment, where `omega` is `app (lam (app (var 0) (var 0))) (lam (app (var 0) (var 0)))`
- WHEN the application is evaluated
- THEN the direct route derives `unbound 0` without a derivation for `omega`, and the interpreter route represents that unbound outcome without evaluating the encoded argument

#### Scenario: An open lambda is a closure

- GIVEN `lam (var 1)` and the empty environment
- WHEN the term is evaluated directly and through the interpreter
- THEN the direct route derives `closure (var 1) []`, and the interpreter route represents that closure

#### Scenario: A diverging term has no derivation

- GIVEN `omega`, defined as `app (lam (app (var 0) (var 0))) (lam (app (var 0) (var 0)))`
- WHEN a derivation at the empty environment is sought
- THEN neither `Direct` nor the interpreter route derives an outcome

#### Scenario: Quoted re-entry is outside the theorem

- GIVEN `quote (var 0)`
- WHEN someone asks whether the metacircular theorem covers it
- THEN `Pure` does not hold, and the theorem does not

### Requirement: The theorem's dependencies are the logic, not an assumption of correctness

`metacircular` and `coverage` SHALL be Lean declarations. Their axiom dependencies SHALL NOT include `sorryAx` and SHALL NOT include an axiom declared by this package. `Direct` SHALL be proved deterministic.

#### Scenario: No admitted correctness

- GIVEN the compiled theorem `metacircular`
- WHEN its axiom dependencies are printed
- THEN `sorryAx` is absent and no axiom from this package is present
