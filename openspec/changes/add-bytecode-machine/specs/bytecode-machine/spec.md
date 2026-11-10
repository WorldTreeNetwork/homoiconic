# bytecode-machine

## ADDED Requirements

### Requirement: Programs compile to flat code

The kernel package SHALL define an instruction set for the `Reflect` language and a total function `compile` from terms to an array of instructions. Code SHALL be representable as a data array of numbers. The package SHALL prove that `decompile (compile t)` returns `t` for every term `t`.

#### Scenario: Code turns back into its term

- GIVEN any term
- WHEN it is compiled and then decompiled
- THEN the result is that term

### Requirement: The machine agrees with direct evaluation

The package SHALL define a machine state and a total function `step` on states. For every term `t` and outcome `o`, the package SHALL prove that `Direct [] t o` holds if and only if the machine, loaded with `compile t`, halts after some number of steps with an outcome that reads back as `o`. A term with no derivation SHALL never halt.

#### Scenario: Identity

- GIVEN `app (lam (var 0)) (lam (var 0))`
- WHEN its code is run
- THEN the machine halts with the identity closure

#### Scenario: Divergence

- GIVEN `omega`
- WHEN its code is run for any number of steps
- THEN the machine has not halted

### Requirement: A run can pause and continue

The package SHALL prove that running `n + m` steps from a state equals running `m` steps from the state reached after `n`. A halted state SHALL step to itself.

#### Scenario: Three slices

- GIVEN a program that halts after `n` steps
- WHEN it is run as three slices whose lengths sum to at least `n`
- THEN the outcome equals the outcome of one run

### Requirement: Steps bound space

The package SHALL prove that the size of the state after `n` steps is at most the size of the starting state plus a stated constant times `n`.

#### Scenario: A budget bounds memory

- GIVEN a step budget
- WHEN any program is run within it
- THEN the state size is within the stated bound

### Requirement: The theorems depend on the logic only

`machine_correct`, `run_add`, `decompile_compile`, and `space_bound` SHALL be restated by a contract file. Their axiom dependencies SHALL NOT include `sorryAx` or an axiom declared by this package.

#### Scenario: No admitted correctness

- GIVEN the compiled theorem `machine_correct`
- WHEN its axiom dependencies are printed
- THEN `sorryAx` is absent and no axiom from this package is present
