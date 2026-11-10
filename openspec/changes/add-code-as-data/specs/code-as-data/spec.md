# code-as-data

## ADDED Requirements

### Requirement: Data is primitive

The kernel package SHALL define a language whose data is natural numbers and arrays of data. A value SHALL be a closure or a data value. An outcome SHALL be a value, `unbound i`, or `wrong`. Evaluation SHALL be call-by-value, function before argument, over de Bruijn terms. Divergence SHALL be the absence of a derivation.

#### Scenario: Data is built in the language

- GIVEN `cons (lit 1) (cons (succ (lit 1)) (lit []))`
- WHEN it is evaluated at the empty environment
- THEN the outcome is the data value `[1, 2]`

#### Scenario: Data is taken apart in the language

- GIVEN a case form whose scrutinee is the literal `[4, 5]` and whose non-empty branch is `cons (var 1) (var 0)`
- WHEN it is evaluated
- THEN the outcome is the data value `[4, 5]`, and the other three branches are not evaluated

#### Scenario: Misuse is an outcome

- GIVEN `app (lit 1) omega`
- WHEN it is evaluated
- THEN the outcome is `wrong`, and `omega` is not evaluated

### Requirement: A literal is a quotation

`lit d` SHALL derive the data value `d` and SHALL NOT inspect `d`. The package SHALL define `reify`, a total function from terms to data. Quoting a program `p` SHALL be `lit (reify p)`. There SHALL NOT be a term that `reify` rejects.

#### Scenario: A quoted program is not run

- GIVEN `lit (reify omega)`
- WHEN it is evaluated
- THEN the outcome is the data value `reify omega`

### Requirement: The interpreter takes a program as data

`interp` SHALL be one closed term of this language. It SHALL NOT mention `Direct` or `evalFuel`. For every term `p` and every outcome `o`, the package SHALL prove that `Direct [] p o` holds if and only if `app interp (lit (reify p))` derives `value (data (reifyOutcome o))` at the empty environment. The package SHALL prove that every outcome of that application is `value (data (reifyOutcome o))` for some `o`. The comparison SHALL be equality of data. It SHALL NOT pass through a decoder.

The statement SHALL have no side condition on `p`. It SHALL cover open terms, diverging terms, terms that go `wrong`, and terms that contain literals.

The package SHALL prove the same statement at every environment, with the environment passed as data.

#### Scenario: A program with a quotation

- GIVEN `lit (reify (app (lam (var 0)) (lam (var 0))))`
- WHEN both routes are derived
- THEN the interpreter route derives the data form of the direct outcome

#### Scenario: A program builds and runs a program

- GIVEN a term that builds the data `[1, 0]` with `cons` and applies `interp` to it
- WHEN it is evaluated directly and through the interpreter
- THEN the direct route derives the data form of the identity closure, and the interpreter route derives the data form of that outcome

#### Scenario: A diverging term has no derivation

- GIVEN `omega`
- WHEN a derivation is sought on either route
- THEN there is none

### Requirement: The interpreter interprets itself to any depth

For every depth `k`, every term `p`, and every outcome `o`, the package SHALL prove that `Direct [] p o` holds if and only if the interpreter applied `k` times derives `o` wrapped as data `k` times.

#### Scenario: Two levels

- GIVEN `app (lam (var 0)) (lam (var 0))`
- WHEN the interpreter interprets itself interpreting that program
- THEN the outcome is the data form of the data form of the identity closure

### Requirement: The theorems depend on the logic only

`reflective`, `reflective_coverage`, `reflective_env`, and `tower` SHALL be Lean declarations restated by a contract file. Their axiom dependencies SHALL NOT include `sorryAx` or an axiom declared by this package. `Direct` SHALL be proved deterministic. `evalFuel` SHALL be proved sound and complete for `Direct`.

#### Scenario: No admitted correctness

- GIVEN the compiled theorem `reflective`
- WHEN its axiom dependencies are printed
- THEN `sorryAx` is absent and no axiom from this package is present
