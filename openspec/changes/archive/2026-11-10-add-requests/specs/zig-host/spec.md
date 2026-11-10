# zig-host

At fold, the overview paragraph also names `reflect_converse` and the command `host/out/ask`.

## MODIFIED Requirements

### Requirement: The host returns the kernel's result
<!-- base: 4489df3bacc2d758a87cf4c04dcda441e3fc4d24 openspec/specs/zig-host/spec.md -->

The Zig host SHALL pass one program's bytes, an output buffer, and a step budget to the Lean export `reflect_run`. That export SHALL read the surface syntax, compile the term, and run the machine for at most the budget. It SHALL write the plain text rendering of the outcome and SHALL return the number of bytes that rendering needs. The Zig sources SHALL pass and print bytes. They SHALL NOT read the syntax and SHALL NOT case-split on terms to produce an outcome. `reflect_run` SHALL NOT answer with a numeric result code. `reflect_run` and `reflect_converse` SHALL be the only exports that evaluate.

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
<!-- base: 4489df3bacc2d758a87cf4c04dcda441e3fc4d24 openspec/specs/zig-host/spec.md -->

The Zig tree SHALL load the Lean exports and SHALL NOT define an evaluator or a reader.

#### Scenario: One evaluator

- GIVEN the Zig sources
- WHEN they are reviewed against the partition
- THEN every outcome comes from the Lean exports `reflect_run` and `reflect_converse`, and no Zig source decides an outcome

## ADDED Requirements

### Requirement: A command runs a program against answers

The host SHALL provide a command that takes the path of a program file, the path of an answers file, and an optional step budget. It SHALL pass both files' bytes and the budget to the Lean export `reflect_converse` and SHALL print the bytes that come back, followed by a newline, on standard output. `reflect_converse` SHALL run `Surface.converseText` and SHALL return the number of bytes the rendering needs, as `reflect_run` does. With no budget given the command SHALL use one hundred million steps for each turn. It SHALL exit 0 whenever the kernel answered and the answer was written, whatever the answer says: requests, a waiting run, a value, an error, and an answers file the kernel refuses are all the kernel's text. It SHALL exit 2 and print one line on standard error, which does not repeat the arguments, when it is called with the wrong number of arguments, when the budget is not a whole number, when either file cannot be read, or when the answer cannot be written. The Zig source SHALL NOT read either file's contents. Each call SHALL run the program from the start against the whole answers file.

#### Scenario: A program asks and finishes

- GIVEN `examples/ask.hom` and `examples/ask.answers`
- WHEN the host check runs the command
- THEN it prints `asked: [1]`, `asked: [2, 20]` and `42`, and exits 0

#### Scenario: A program is left waiting

- GIVEN `examples/ask.hom` and `examples/ask-one.answers`
- WHEN the host check runs the command
- THEN it prints the two `asked:` lines and `waiting`, and exits 0

#### Scenario: A missing answers file

- GIVEN a path to an answers file that does not exist
- WHEN the command is run
- THEN it exits 2 with one line on standard error and nothing on standard output
