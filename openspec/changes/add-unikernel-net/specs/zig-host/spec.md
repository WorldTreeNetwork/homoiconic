# zig-host

## MODIFIED Requirements

### Requirement: The host returns the kernel's result
<!-- base: d5070aae7ac67c342adc029f97343535f047af6d openspec/specs/zig-host/spec.md -->

The Zig host SHALL pass one program's bytes, an output buffer, and a step budget to the Lean export `reflect_run`. That export SHALL read the surface syntax, compile the term, and run the machine for at most the budget. It SHALL write the plain text rendering of the outcome and SHALL return the number of bytes that rendering needs. The Zig sources SHALL pass and print bytes. They SHALL NOT read the syntax and SHALL NOT case-split on terms to produce an outcome. `reflect_run` SHALL NOT answer with a numeric result code. The exports that evaluate SHALL be `reflect_run`, `reflect_converse`, `reflect_run_bytes`, `reflect_keep_start`, `reflect_keep_answer`, `reflect_keep_give`, `reflect_channels` and `reflect_reply_bytes`, and each SHALL be a Lean definition.

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


## ADDED Requirements

### Requirement: A Lean export returns a bounded run as bytes

The Lean definition exported as `reflect_reply_bytes` SHALL take a program pointer and length, output pointer and capacity, and UInt64 step budget. It SHALL run `Surface.replyBytes`, which decodes program bytes, runs the existing compiled machine and returns `Wire.runReplyBytes` for its reply. It SHALL be an export that evaluates. It SHALL return the required length, writing nothing when capacity is insufficient, as the existing byte exports do. The caller SHALL pass and copy bytes and SHALL NOT infer an outcome from text. Machine-step budgets SHALL NOT be described as native wall-clock bounds.

#### Scenario: A complete binary answer

- GIVEN identical program bytes and budget passed to the server and the Linux comparison process
- WHEN each calls reflect_reply_bytes
- THEN each receives the identical complete wire-bytes run reply, and an insufficient buffer remains untouched
