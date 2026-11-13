## ADDED Requirements

### Requirement: A command runs a program through the interpreter

The run command SHALL accept `--interp` and `--interp=k`, for a whole number `k`, before the file path, in either order with `--bytes`. `--interp` SHALL mean `--interp=1`. With it, the program, from source or from its byte form, SHALL be passed to the export `reflect_interp`, a Lean definition, which SHALL run `level k` of the program on the machine for at most the budget: the closed interpreter term given the program as data, `k` times over. The export SHALL read the answer back through `k` levels of the outcome's data form and SHALL render it as `reflect_run` renders an outcome. `reflect_interp` SHALL be one of the exports that evaluate. Zig SHALL NOT read the program or the answer.

#### Scenario: The interpreter prints what the program prints

- GIVEN `examples/append.hom`, `examples/code.hom`, `examples/factorial.hom`, the identity function and a program whose outcome is wrong
- WHEN the command is run on each directly, and with `--interp=0`, `--interp=1` and `--interp=2`, from source and with `--bytes` on its byte form
- THEN every run prints the same text

#### Scenario: The budget counts the outermost machine

- GIVEN `examples/forever.hom`
- WHEN the command is run on it with `--interp` and a budget of 5000
- THEN it prints `no result within 5000 steps`

#### Scenario: Bad levels are refused

- WHEN the command is run with `--interp=x`
- THEN it prints `run: the interpreter levels must be a whole number` on standard error, nothing on standard output, and exits 2
