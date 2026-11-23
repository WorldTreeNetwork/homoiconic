# code-as-data

What is built: a Lean library, `Reflect`, in the kernel package; with `Surface` it is one of the package's two libraries. Data is natural numbers, arrays, text and names, a program is quoted as `lit (reify p)`, and `interp` is one closed term that takes a program as data. A text is a list of Unicode scalar values (`Data.text`, over `List Char`, with the three functions of `kernel/Reflect/Text.lean`); `case` and `cons` see it as the list of its code points. A name carries a number (`Data.name`); `case`, `succ` and the operation number of `prim` see it as that number, and nothing else does. `Direct` has twelve rules for the two kinds beside the thirty it had; `interp` and `evalTerm` were not edited for them (`openspec/changes/archive/2026-11-17-add-data-kinds/`). `reflective`, `reflective_coverage`, `reflective_env`, and `tower` are proved for every term, with no side condition, and restated in `kernel/ReflectContract.lean`; their statements did not change when the two kinds were added, and `kernel/InterpGate.lean` checks them importing `Reflect.Correctness` alone. `prim c x` runs an operation from a table, `Ops`, that the evaluation definitions and the theorems about them take as a parameter. The first table, `arith`, has operations 0 to 8; `text` (7) and `codes` (8) go between a text and the array of its code points.

## Purpose

Name the language in which a program is a value, and the interpreter theorem in that setting. This spec does not contain the bytecode machine (`openspec/specs/bytecode-machine/spec.md`) or the Zig host.

## Requirements

### Requirement: Data is primitive

The kernel package SHALL define a language whose data is natural numbers, arrays of data, text, and names. A text is a sequence of Unicode scalar values; its code points, below, are the numbers of those. A name carries a number. A value SHALL be a closure or a data value. An outcome SHALL be a value, `unbound i`, or `wrong`. Evaluation SHALL be call-by-value, function before argument, over de Bruijn terms. Divergence SHALL be the absence of a derivation.

The successor, construction, case analysis and the operation number of `prim` SHALL see every data value as a number or as a list. Case analysis SHALL take a branch on every data value: the zero or the successor branch on a value seen as a number, the empty or the non-empty branch on a value seen as a list. The successor, the tail of a construction and the operation number of `prim` SHALL go `wrong` on a data value exactly where its view does: the successor and the operation number of `prim` on a value seen as a list, the tail of a construction on a value seen as a number. The head of a construction SHALL be any data value.

A name SHALL be seen as its number. It SHALL be accepted as that number by the successor, by case analysis and as the operation number of `prim`, and nowhere else: an operation of a table is handed the name itself as its argument. The successor of a name with number `k` SHALL be the number `k + 1`. Case analysis on a name SHALL take the zero branch when its number is 0 and otherwise the successor branch with the number one less bound. Construction onto a name SHALL be `wrong`. None of these SHALL give a name.

A text SHALL be seen as the list of its code points. Case analysis on the empty text SHALL take the empty branch. On any other text it SHALL take the non-empty branch with the first code point, a number, as the head and the rest, a text, as the tail. Construction of a data value onto a text SHALL give the array of that value followed by the code points of the text. The successor of a text SHALL be `wrong`.

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

#### Scenario: Text is taken apart as a list

- GIVEN a case form whose scrutinee is the literal text `"hé"` and whose non-empty branch is `cons (var 1) (cons (var 0) (lit []))`
- WHEN it is evaluated
- THEN the outcome is the array of the number 104 and the text `"é"`

#### Scenario: Consing onto text gives an array

- GIVEN `cons (lit 1) (lit "a")`
- WHEN it is evaluated
- THEN the outcome is the array `[1, 97]`, and it is not a text

#### Scenario: A name is seen as its number

- GIVEN the literal of the name with number 3
- WHEN its successor is taken, when it is the scrutinee of a case form whose successor branch is `var 0`, and when the number 1 is consed onto it
- THEN the outcomes are the number 4, the number 2, and `wrong`

#### Scenario: A view that does not fit is wrong

- GIVEN `succ (lit "a")`, `cons (lit 1) (lit n)` with `n` the name with number 3, and `prim (lit "a") omega`
- WHEN each is evaluated
- THEN each outcome is `wrong`, and `omega` is not evaluated

#### Scenario: A text or a name as a head

- GIVEN `cons (lit "a") (lit [])` and `cons (lit n) (lit [])` with `n` the name with number 3
- WHEN each is evaluated
- THEN the outcomes are the array of the text `"a"` and the array of that name

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

The language SHALL have a construct `prim c x`. Evaluation SHALL evaluate `c` first. An error outcome of `c` SHALL be the outcome, and `x` SHALL NOT be evaluated. If `c` evaluates to a function, an array or a text, the outcome SHALL be `wrong`, and `x` SHALL NOT be evaluated. Otherwise `c` evaluates to a number `k`, or to a name whose number is `k`, and `x` is evaluated. An error outcome of `x` SHALL be the outcome. If `x` evaluates to a function, the outcome SHALL be `wrong`. Otherwise `x` evaluates to a data value `d`, and the outcome SHALL be the data value `op k d`.

`op` SHALL come from a table, `Ops`, that holds one total function from a number and a data value to a data value. The table SHALL also hold `cost`, the charge a priced budget makes for an operation (`openspec/specs/bytecode-machine/spec.md`), one when a table does not give it; `Direct`, `evalFuel`, `interp` and the theorems of this spec SHALL NOT read it. `Direct`, `evalFuel`, and every theorem this spec names about them SHALL take the table as a parameter and SHALL hold for every table. `reify (prim c x)` SHALL be `[6, reify c, reify x]`.

`interp` and `evalTerm` SHALL be the same terms for every table. Adding an operation to a table SHALL NOT require a change to the interpreter or to a proof.

`kernel/ReflectContract.lean` SHALL state each theorem with the table universally quantified and SHALL NOT import a table.

#### Scenario: An operation agrees at every level

- GIVEN the table `arith` and the program `prim 0 [2, 3]`
- WHEN it is evaluated directly, through the interpreter, and through the interpreter interpreting itself
- THEN each gives 5, in the data form for its level

#### Scenario: A bad operation number stops before the argument

- GIVEN `prim c x` where `c` is a function, an array, a text, or an unbound variable, and `x` does not terminate
- WHEN it is evaluated
- THEN the outcome is `wrong`, `wrong`, `wrong`, or `unbound`, and it is the same through the interpreter

#### Scenario: The operation number is computed

- GIVEN `prim (succ 0) [9, 4]` and the table `arith`
- WHEN it is evaluated
- THEN the outcome is 5, the answer of operation 1

#### Scenario: A name as an operation number is its number

- GIVEN `prim c [2, 3]` where `c` is the literal of the name with number 0, and the table `arith`
- WHEN it is evaluated directly and through the interpreter
- THEN each gives 5, in the data form for its level

### Requirement: The first table is exact arithmetic

The package SHALL define a table `arith`. On a two-item array of numbers it SHALL answer: 0, the sum; 1, the difference, or 0 when the second is larger; 2, the product; 3, the quotient rounded down, or 0 when the divisor is 0; 4, the remainder, or the first number when the divisor is 0; 6, 1 when the first is less than the second and 0 otherwise. Operation 5 SHALL take any two data values and answer 1 when they are equal and 0 otherwise; a text SHALL NOT equal an array, and a name SHALL NOT equal a number. The operands of operations 0 to 4 and 6 SHALL be plain numbers: a name is not one, and on a two-item array that holds a name these operations SHALL answer the empty array. Operation 7 SHALL answer, for an array whose items are all numbers that are Unicode scalar values, the text of those code points, and for a text, that text. Operation 8 SHALL answer, for a text, the array of its code points, and for an array whose items are all numbers that are Unicode scalar values, that array. Numbers SHALL be exact at any size. For any other number or argument, `arith` SHALL answer the empty array. No operation SHALL answer a name that is not in its argument. No theorem SHALL depend on `arith`.

#### Scenario: Large numbers are exact

- GIVEN a program that multiplies 2 by itself 100 times with operation 2
- WHEN it runs
- THEN the result is 1267650600228229401496703205376

#### Scenario: An unknown operation answers the empty array

- GIVEN operation number 99, or operation 0 given `[1, [2]]`
- WHEN it runs under `arith`
- THEN the result is `[]`

#### Scenario: Equality tells the kinds apart

- GIVEN the text `"a"` and the array `[97]`; the empty text and `[]`; the name with number 3 and the number 3
- WHEN operation 5 compares each pair
- THEN each answer is 0

#### Scenario: A name is not an arithmetic operand

- GIVEN the two-item array of the name with number 3 and the number 0, and the array `[3, 0]`
- WHEN operation 0 runs on each
- THEN the first answer is `[]` and the second is 3

#### Scenario: Text to code points and back

- GIVEN the text `"hé"`
- WHEN operation 8 runs on it, and operation 7 on the result
- THEN the first answer is `[104, 233]` and the second is the text `"hé"`

#### Scenario: A number that is no scalar value

- GIVEN the array `[55296]`, a surrogate
- WHEN operation 7 runs on it
- THEN the answer is `[]`

### Requirement: The theorems depend on the logic only

`reflective`, `reflective_coverage`, `reflective_env`, and `tower` SHALL be Lean declarations restated by a contract file. Their axiom dependencies SHALL NOT include `sorryAx` or an axiom declared by this package. `Direct` SHALL be proved deterministic. `evalFuel` SHALL be proved sound and complete for `Direct`.

#### Scenario: No admitted correctness

- GIVEN the compiled theorem `reflective`
- WHEN its axiom dependencies are printed
- THEN `sorryAx` is absent and no axiom from this package is present

### Requirement: The interpreter is unchanged by text and names

`interp` and `evalTerm` SHALL be the terms they were before `Data` had text and names. `reflective`, `reflective_coverage`, `reflective_env` and `tower` SHALL hold with their statements unchanged, for every term, among them terms whose literals are or contain text and names. `kernel/ReflectContract.lean` SHALL check without having been edited, against modules built from the sources as they are.

#### Scenario: A program that goes wrong on text

- GIVEN `succ (lit "a")`
- WHEN both routes are derived
- THEN the direct outcome is `wrong` and the interpreter derives the data `[2]`

#### Scenario: A program that takes a name apart

- GIVEN a case form whose scrutinee is the literal of the name with number 1 and whose successor branch is `succ (var 0)`
- WHEN both routes are derived
- THEN the direct outcome is the number 1 and the interpreter derives `[0, [1, 1]]`

#### Scenario: The contract is not edited

- GIVEN `kernel/ReflectContract.lean`, `kernel/Reflect/Interpreter.lean` and `kernel/Reflect/Correctness.lean` as they were before this change
- WHEN `lake build` has exited 0 and then `lake env lean ReflectContract.lean` runs
- THEN it exits 0
