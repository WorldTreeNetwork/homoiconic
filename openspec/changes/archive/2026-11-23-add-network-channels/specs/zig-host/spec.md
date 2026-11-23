# zig-host delta: the remote-channel exports

## MODIFIED Requirements

### Requirement: The host returns the kernel's result
<!-- base: 32f164303decd82f500d75fdbc0a0363f02795b6 openspec/specs/zig-host/spec.md -->

The Zig host SHALL pass one program's bytes, an output buffer, and a step budget to the Lean export `reflect_run`. That export SHALL read the surface syntax, compile the term, and run the machine for at most the budget. It SHALL write the plain text rendering of the outcome and SHALL return the number of bytes that rendering needs. The Zig sources SHALL pass and print bytes. They SHALL NOT read the syntax and SHALL NOT case-split on terms to produce an outcome. `reflect_run` SHALL NOT answer with a numeric result code. The exports that evaluate SHALL be `reflect_run`, `reflect_converse`, `reflect_run_bytes`, `reflect_interp`, `reflect_keep_start`, `reflect_keep_answer`, `reflect_keep_give`, `reflect_channels`, `reflect_vm_start`, `reflect_vm_from`, `reflect_node_start`, `reflect_node_from`, `reflect_reply_bytes`, `reflect_remote_offer`, `reflect_remote_take`, `reflect_remote_log` and `reflect_remote_same`, and each SHALL be a Lean definition.

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

### Requirement: Lean exports carry the remote channel

The Lean definitions exported as `reflect_remote_offer(out, capacity)`, `reflect_remote_take(offer, length, out, capacity)` and `reflect_remote_log(out, capacity)` SHALL give `Surface.Remote.offerBytes`, `Surface.Remote.takeBytes` of the bytes lent, and the UTF-8 of `Surface.Remote.logText` (`openspec/specs/channels/spec.md`). Each SHALL return the number of bytes needed and write nothing when they do not fit, as the other byte exports do. `reflect_remote_same(unused)` SHALL return 1 when `Surface.Remote.same` holds and 0 otherwise (`kernel/Surface/Host.lean`). The network guests call the first three (`openspec/specs/unikernel-net/spec.md`); `unikernel/out/remote-check` calls the fourth and exits 0 only on 1.

#### Scenario: The same answer outside a guest

- GIVEN `unikernel/out/remote-check`, linked from the objects the guests link
- WHEN `unikernel/check-wire.sh` runs it
- THEN it exits 0
