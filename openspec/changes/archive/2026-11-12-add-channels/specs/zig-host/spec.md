# zig-host

## ADDED Requirements

### Requirement: A command runs a program as processes

The host SHALL provide a command that takes a program file, an optional schedule file or `-` for none, an optional step budget and an optional event limit. It SHALL pass the program's bytes, the schedule's bytes, the budget and the limit to the Lean export `reflect_channels` and SHALL print the text that comes back and a newline. With no schedule the kernel SHALL choose the events, at most the limit. With a schedule the kernel SHALL run exactly its events and stop at the first that cannot happen. The text SHALL be the schedule that happened, in the form a schedule file is written in, then one line for each process with what it finished with or is waiting on and the names it holds, then how the run stopped. A printed schedule given back SHALL run the same events and print the same schedule and process lines; the last line SHALL be the same when the first run was not refused and did not run out of budget. The host SHALL NOT read the program or the schedule, SHALL NOT choose an event, and SHALL exit 0 whenever the kernel answered. It SHALL exit 2 with a message on standard error for a wrong call, a file it cannot read, or a schedule file that is empty.

#### Scenario: A recorded schedule replays

- GIVEN `examples/ping.hom`
- WHEN it is run with no schedule, the schedule line of the output is saved to a file, and it is run again with that file
- THEN the two outputs are the same bytes

#### Scenario: A refused event is the kernel's text

- GIVEN `examples/guess.hom` and `examples/guess.schedule`
- WHEN the command runs
- THEN the last line is `refused: [2, 0, 1] cannot happen` and the command exits 0

#### Scenario: Choosing stops at the limit

- GIVEN `examples/spawns.hom`, which starts processes without end, and an event limit of 3
- WHEN the command runs with no schedule
- THEN three events happen, four processes are listed, and the last line is `an event is offered`

## MODIFIED Requirements

### Requirement: The host returns the kernel's result
<!-- base: 3923633905d7fb798ce3ad458a6396a062f48c6d openspec/specs/zig-host/spec.md -->

The Zig host SHALL pass one program's bytes, an output buffer, and a step budget to the Lean export `reflect_run`. That export SHALL read the surface syntax, compile the term, and run the machine for at most the budget. It SHALL write the plain text rendering of the outcome and SHALL return the number of bytes that rendering needs. The Zig sources SHALL pass and print bytes. They SHALL NOT read the syntax and SHALL NOT case-split on terms to produce an outcome. `reflect_run` SHALL NOT answer with a numeric result code. The exports that evaluate SHALL be `reflect_run`, `reflect_converse`, `reflect_run_bytes`, `reflect_keep_start`, `reflect_keep_answer`, `reflect_keep_give` and `reflect_channels`, and each SHALL be a Lean definition.

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
<!-- base: 3923633905d7fb798ce3ad458a6396a062f48c6d openspec/specs/zig-host/spec.md -->

The Zig tree SHALL load the Lean exports and SHALL NOT define an evaluator or a reader.

#### Scenario: One evaluator

- GIVEN the Zig sources
- WHEN they are reviewed against the partition
- THEN every outcome comes from a Lean export, and no Zig source decides an outcome
