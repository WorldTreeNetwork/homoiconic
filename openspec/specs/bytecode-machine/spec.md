# bytecode-machine

What is built: `Reflect.Machine`, a stack machine for the `Reflect` language. `compile` takes a term to continuation-form code, `step` is total on an explicit state, and `run n` takes `n` steps. `machine_correct`, `machine_exact`, `machine_never_halts`, `run_add`, `run_halted`, `runUntil_eq`, `decompile_compile`, and `depth_bound` are proved and restated in `kernel/MachineContract.lean`. `step`, `run`, and the theorems about them take the operation table `Ops` as a parameter and hold for every table. The speed measurement is in `docs/LEARNINGS.md`. The host runs `Reflect` programs on this machine through `reflect_run` (`openspec/specs/zig-host/spec.md`).

## Purpose

Name the machine that runs `Reflect` programs one step at a time, and its agreement with direct evaluation. This spec does not contain the language or the interpreter theorem (`openspec/specs/code-as-data/spec.md`), flattening to an array, serialized states, or a native executor.

## Requirements

### Requirement: Programs compile to code

The kernel package SHALL define an instruction set for the `Reflect` language and a total function `compile` from terms to code. The package SHALL prove that `decompile (compile t)` returns `t` for every term `t`.

#### Scenario: Code turns back into its term

- GIVEN any term
- WHEN it is compiled and then decompiled
- THEN the result is that term

### Requirement: The machine agrees with direct evaluation

The package SHALL define a machine state and a total function `step` on states. For every term `t` and outcome `o`, the package SHALL prove that `Direct [] t o` holds if and only if the machine, loaded with `compile t`, halts after some number of steps with an outcome that reads back as `o`. The package SHALL prove that whatever the machine halts with is exactly the compiled form of a source outcome, so that a returned closure holds the compiled code of its body. The package SHALL prove that a term with no derivation never halts.

#### Scenario: Identity

- GIVEN `app (lam (var 0)) (lam (var 0))`
- WHEN its code is run for seven steps
- THEN the machine has halted with the compiled identity closure

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

### Requirement: Steps bound control depth

The package SHALL prove that the value stack plus the pending frames after `n` steps is at most that of the starting state plus `n`.

#### Scenario: A budget bounds the stacks

- GIVEN a step budget
- WHEN any program is run within it
- THEN the stack and frame depth is within the stated bound

### Requirement: The machine runs operations

`compile` SHALL compile `prim c x` to the code of `c`, an instruction that checks the value on top is a number, the code of `x`, and an instruction that replaces the number and the argument with the table's answer. A value that fails the check SHALL halt the machine with `wrong` before the code of `x` runs. `step` and `run` SHALL take the table as a parameter. `machine_correct`, `machine_exact`, `machine_never_halts`, `run_add`, `run_halted`, `runUntil_eq`, and `depth_bound` SHALL hold for every table. An operation SHALL be one step.

#### Scenario: An operation on the machine

- GIVEN each operation scenario in `kernel/ReflectRun.lean`
- WHEN the compiled program runs on the machine, whole and in three slices
- THEN the halted outcome reads back as the outcome of direct evaluation

#### Scenario: Code with an operation turns back into its term

- GIVEN a term that contains `prim`
- WHEN it is compiled and decompiled
- THEN the result is the term

### Requirement: The theorems depend on the logic only

`machine_correct`, `machine_exact`, `machine_never_halts`, `run_add`, `run_halted`, `runUntil_eq`, `decompile_compile`, and `depth_bound` SHALL be restated by a contract file. Their axiom dependencies SHALL NOT include `sorryAx` or an axiom declared by this package.

#### Scenario: No admitted correctness

- GIVEN the compiled theorem `machine_correct`
- WHEN its axiom dependencies are printed
- THEN `sorryAx` is absent and no axiom from this package is present
