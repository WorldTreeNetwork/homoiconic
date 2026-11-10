# zig-host

At fold, the overview paragraph also drops its sentence about `kernel_run` and no longer names `lean-kernel`.

## MODIFIED Requirements

### Requirement: The host returns the kernel's result
<!-- base: 9ba83e77d021f4e5576f4c14db43a58cb170906a openspec/specs/zig-host/spec.md -->

The Zig host SHALL pass one program's bytes, an output buffer, and a step budget to the Lean export `reflect_run`. That export SHALL read the surface syntax, compile the term, and run the machine for at most the budget. It SHALL write the plain text rendering of the outcome and SHALL return the number of bytes that rendering needs. The Zig sources SHALL pass and print bytes. They SHALL NOT read the syntax and SHALL NOT case-split on terms to produce an outcome. `reflect_run` SHALL NOT answer with a numeric result code. `reflect_run` SHALL be the only export that evaluates.

#### Scenario: Identity

- GIVEN a program that binds the identity function and applies it to itself
- WHEN the Zig check runs it through `reflect_run`
- THEN the printed text is `<function>`

#### Scenario: An unbound index is reported in full

- GIVEN the term `var 2147483647`, which no surface text reads as
- WHEN the Lean check compiles it, runs the machine, and renders the state
- THEN the text is `error: unbound 2147483647`, and it differs from the text for a run with no result

#### Scenario: Data comes back

- GIVEN the append program in `examples/append.hom`
- WHEN the host check runs it through the command
- THEN the printed text is `[1, 2, 3, 4]`

#### Scenario: A diverging term has no result

- GIVEN the program `let w = fn x -> x x` followed by `w w`
- WHEN the Zig check runs it with a finite budget
- THEN the printed text says there is no result within that many steps, and the call returns

#### Scenario: A malformed program is refused

- GIVEN text that is not a program
- WHEN the Zig check passes it
- THEN the printed text is a syntax error with a line and column, and nothing is run

#### Scenario: A zero byte does not end a program

- GIVEN the three bytes `4`, `2`, and zero
- WHEN the Zig check passes them
- THEN the printed text is a syntax error at column 3, not `42`

#### Scenario: Bytes past the length are not read

- GIVEN a buffer holding `42invalid` and a declared length of 2
- WHEN the Zig check passes it
- THEN the printed text is `42`

### Requirement: The host contains no evaluator
<!-- base: 9ba83e77d021f4e5576f4c14db43a58cb170906a openspec/specs/zig-host/spec.md -->

The Zig tree SHALL load the Lean exports and SHALL NOT define an evaluator or a reader.

#### Scenario: One evaluator

- GIVEN the Zig sources
- WHEN they are reviewed against the partition
- THEN every outcome comes from the Lean export `reflect_run`, and no Zig source decides an outcome

## ADDED Requirements

### Requirement: A command runs a program file

The host SHALL provide a command that takes the path of a program file and an optional step budget. It SHALL pass the file's bytes and the budget to `reflect_run` and SHALL print the bytes that come back, followed by a newline, on standard output. With no budget given it SHALL use one hundred million steps. It SHALL exit 0 whenever the kernel answered and the answer was written, whatever the answer says: a value, an error outcome, a syntax error, and a run with no result are all the kernel's text. It SHALL exit 2 and print one line on standard error, which does not repeat the arguments, when it is called with the wrong number of arguments, when the budget is not a whole number, when the file cannot be read, or when the answer cannot be written. An answer longer than the first buffer SHALL be printed in full.

#### Scenario: A program file runs

- GIVEN `examples/append.hom`
- WHEN the command is run on it
- THEN it prints `[1, 2, 3, 4]` and exits 0

#### Scenario: The budget is an argument

- GIVEN `examples/forever.hom`, which does not finish
- WHEN the command is run on it with the budget `5000`
- THEN it prints `no result within 5000 steps` and exits 0

#### Scenario: A long answer is printed in full

- GIVEN a program whose answer is an array of the numbers 20000 down to 1
- WHEN the command is run on it
- THEN it prints all 128894 bytes of the array and a newline

#### Scenario: A file that cannot be read

- GIVEN a path that names no file, or names a directory
- WHEN the command is run on it
- THEN it prints nothing on standard output, one line on standard error, and exits 2

#### Scenario: A wrong call

- GIVEN no arguments, three arguments, the budget `-1`, or a budget that contains a line break
- WHEN the command is run
- THEN it prints nothing on standard output, one line on standard error, and exits 2
