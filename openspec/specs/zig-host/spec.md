# zig-host

What is built: a Zig host that passes one program's text, an output buffer, and a step budget to the Lean export `reflect_run`. That export reads the surface syntax (`openspec/specs/surface-syntax/spec.md`), runs the proved machine (`openspec/specs/bytecode-machine/spec.md`) for at most the budget, and writes back a plain text rendering of the outcome. The host runs with the operation table `arith` (`openspec/specs/code-as-data/spec.md`). The host links the Lean object, calls the runtime initializer, and contains no evaluator and no reader. The command `host/out/run <program-file> [step-budget]`, built by `host/check.sh`, runs a program file through `reflect_run` and prints the answer. A second export, `reflect_converse`, runs a program against a list of answers (`openspec/specs/requests/spec.md`), and the command `host/out/ask <program-file> <answers-file> [step-budget]`, also built by `host/check.sh`, prints the requests it makes and how it ends. A third, `reflect_run_bytes`, runs a program given in its byte form (`openspec/specs/wire-bytes/spec.md`); `host/out/run --bytes` calls it. A fourth, `reflect_source_bytes`, evaluates nothing: it reads a program's source and gives its byte form, and the command `host/out/bytes <program-file>` writes that to standard output. The interpreter theorems are in `openspec/specs/code-as-data/spec.md` and the machine's in `openspec/specs/bytecode-machine/spec.md`. The append program is `examples/append.hom`; the identity and self-application programs these scenarios name are in `kernel/Surface/Expect.lean`.

## Purpose

Name the host call into the kernel. This spec does not restate the surface syntax, the machine, the interpreter theorems, or the language partition.

## Requirements

### Requirement: The host returns the kernel's result

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

The Zig tree SHALL load the Lean exports and SHALL NOT define an evaluator or a reader.

#### Scenario: One evaluator

- GIVEN the Zig sources
- WHEN they are reviewed against the partition
- THEN every outcome comes from the Lean exports `reflect_run`, `reflect_converse` and `reflect_run_bytes`, and no Zig source decides an outcome

### Requirement: The link is the proved object path

The host SHALL link by the object path recorded in `docs/spikes/lean-c-abi/`. The host SHALL call the Lean runtime initializer on the path that allocates. The build SHALL NOT depend on `dlopen`.

#### Scenario: The test links

- GIVEN the Lean object and the Zig object
- WHEN `leanc` links them and the Zig test runs
- THEN the test exits 0

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

### Requirement: A command runs a program given as bytes

The run command SHALL accept `--bytes` before the file path. With it, the file SHALL be passed to `reflect_run_bytes` as a program in its byte form, and the command SHALL otherwise behave as it does for a source file. Bytes that are not the one form of a value, and a value that is no program, SHALL be the kernel's text and exit 0.

#### Scenario: The same answer from bytes

- GIVEN each example program and its byte form
- WHEN the command is run on the source, and with `--bytes` on the byte form
- THEN both print the same text

#### Scenario: Bytes in a longer form

- GIVEN a file holding the bytes `18 17`
- WHEN the command is run on it with `--bytes`
- THEN it prints `bytes error: a number or length is not in its shortest form` and exits 0

### Requirement: A command writes a program's byte form

The host SHALL provide a command that takes the path of a program file, passes its bytes to `reflect_source_bytes`, and writes the byte form that comes back to standard output, with nothing added. The host SHALL NOT make or inspect the byte form. On a syntax error it SHALL write nothing to standard output, write the kernel's text to standard error, and exit 1. It SHALL exit 2 with one line on standard error when it is called with the wrong number of arguments or cannot read the file.

#### Scenario: Three bytes

- GIVEN a file holding `fn x -> x`
- WHEN the command is run on it
- THEN standard output is the bytes `82 01 00`

#### Scenario: A syntax error

- GIVEN a file holding `fn x ->`
- WHEN the command is run on it
- THEN standard output is empty, standard error starts with `syntax error: `, and the exit is 1
