# code-as-data

At fold, the overview gains: "`prim c x` runs an operation from a table, `Ops`, that every definition and theorem takes as a parameter."

## ADDED Requirements

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
