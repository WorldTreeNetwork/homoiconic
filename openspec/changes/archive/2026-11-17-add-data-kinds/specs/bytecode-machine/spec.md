## MODIFIED Requirements

### Requirement: The machine runs operations
<!-- base: 089c62678014a00cdab2e7db79ca6dfd61b46e41 openspec/specs/bytecode-machine/spec.md -->

`compile` SHALL compile `prim c x` to the code of `c`, an instruction that checks the value on top is a number or a name, the code of `x`, and an instruction that replaces that value and the argument with the table's answer for its number. A value that fails the check SHALL halt the machine with `wrong` before the code of `x` runs. `step` and `run` SHALL take the table as a parameter. `machine_correct`, `machine_exact`, `machine_never_halts`, `run_add`, `run_halted`, `runUntil_eq`, and `depth_bound` SHALL hold for every table, with their statements unchanged by text and names. The instruction set SHALL be unchanged by text and names. An operation SHALL be one step.

#### Scenario: An operation on the machine

- GIVEN each operation scenario in `kernel/ReflectRun.lean`
- WHEN the compiled program runs on the machine, whole and in three slices
- THEN the halted outcome reads back as the outcome of direct evaluation

#### Scenario: Code with an operation turns back into its term

- GIVEN a term that contains `prim`
- WHEN it is compiled and decompiled
- THEN the result is the term

#### Scenario: Text and names on the machine

- GIVEN each text and name scenario in `kernel/ReflectRun.lean`
- WHEN the compiled program runs on the machine, whole and in three slices
- THEN the halted outcome reads back as the outcome of direct evaluation
