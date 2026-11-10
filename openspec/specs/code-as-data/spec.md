# code-as-data

What is built: a Lean library, `Reflect`, in the kernel package; with `Surface` it is one of the package's two libraries. Data is natural numbers and arrays, a program is quoted as `lit (reify p)`, and `interp` is one closed term that takes a program as data. `reflective`, `reflective_coverage`, `reflective_env`, and `tower` are proved for every term, with no side condition, and restated in `kernel/ReflectContract.lean`. `prim c x` runs an operation from a table, `Ops`, that the evaluation definitions and the theorems about them take as a parameter.

## Purpose

Name the language in which a program is a value, and the interpreter theorem in that setting. This spec does not contain the bytecode machine (`openspec/specs/bytecode-machine/spec.md`) or the Zig host.

## Requirements

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

The package SHALL prove the same equivalence at every environment for `evalTerm`, the evaluator term that takes a program and an environment as data. `interp` SHALL be `evalTerm` applied at the empty environment.

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

### Requirement: Operations come from a table

The language SHALL have a construct `prim c x`. Evaluation SHALL evaluate `c` first. An error outcome of `c` SHALL be the outcome, and `x` SHALL NOT be evaluated. If `c` evaluates to a function or an array, the outcome SHALL be `wrong`, and `x` SHALL NOT be evaluated. Otherwise `c` evaluates to a number `k`, and `x` is evaluated. An error outcome of `x` SHALL be the outcome. If `x` evaluates to a function, the outcome SHALL be `wrong`. Otherwise `x` evaluates to a data value `d`, and the outcome SHALL be the data value `op k d`.

`op` SHALL come from a table, `Ops`, that holds one total function from a number and a data value to a data value. `Direct`, `evalFuel`, and every theorem this spec names about them SHALL take the table as a parameter and SHALL hold for every table. `reify (prim c x)` SHALL be `[6, reify c, reify x]`.

`interp` and `evalTerm` SHALL be the same terms for every table. Adding an operation to a table SHALL NOT require a change to the interpreter or to a proof.

`kernel/ReflectContract.lean` SHALL state each theorem with the table universally quantified and SHALL NOT import a table.

#### Scenario: An operation agrees at every level

- GIVEN the table `arith` and the program `prim 0 [2, 3]`
- WHEN it is evaluated directly, through the interpreter, and through the interpreter interpreting itself
- THEN each gives 5, in the data form for its level

#### Scenario: A bad operation number stops before the argument

- GIVEN `prim c x` where `c` is a function, an array, or an unbound variable, and `x` does not terminate
- WHEN it is evaluated
- THEN the outcome is `wrong`, `wrong`, or `unbound`, and it is the same through the interpreter

#### Scenario: The operation number is computed

- GIVEN `prim (succ 0) [9, 4]` and the table `arith`
- WHEN it is evaluated
- THEN the outcome is 5, the answer of operation 1

### Requirement: The first table is exact arithmetic

The package SHALL define a table `arith`. On a two-item array of numbers it SHALL answer: 0, the sum; 1, the difference, or 0 when the second is larger; 2, the product; 3, the quotient rounded down, or 0 when the divisor is 0; 4, the remainder, or the first number when the divisor is 0; 6, 1 when the first is less than the second and 0 otherwise. Operation 5 SHALL take any two data values and answer 1 when they are equal and 0 otherwise. Numbers SHALL be exact at any size. For any other number or argument, `arith` SHALL answer the empty array. No theorem SHALL depend on `arith`.

#### Scenario: Large numbers are exact

- GIVEN a program that multiplies 2 by itself 100 times with operation 2
- WHEN it runs
- THEN the result is 1267650600228229401496703205376

#### Scenario: An unknown operation answers the empty array

- GIVEN operation number 99, or operation 0 given `[1, [2]]`
- WHEN it runs under `arith`
- THEN the result is `[]`

### Requirement: The theorems depend on the logic only

`reflective`, `reflective_coverage`, `reflective_env`, and `tower` SHALL be Lean declarations restated by a contract file. Their axiom dependencies SHALL NOT include `sorryAx` or an axiom declared by this package. `Direct` SHALL be proved deterministic. `evalFuel` SHALL be proved sound and complete for `Direct`.

#### Scenario: No admitted correctness

- GIVEN the compiled theorem `reflective`
- WHEN its axiom dependencies are printed
- THEN `sorryAx` is absent and no axiom from this package is present
