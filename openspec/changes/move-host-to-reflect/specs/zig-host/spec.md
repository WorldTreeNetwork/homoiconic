# zig-host

## MODIFIED Requirements

### Requirement: The host returns the kernel's result
<!-- base: 9dc954b44700851545a7c1a71d05b2ce4d20612b openspec/specs/zig-host/spec.md -->

The Zig host SHALL pass one program's bytes, an output buffer, and a step budget to the Lean export `reflect_run`. That export SHALL read the surface syntax, compile the term, and run the machine for at most the budget. It SHALL write the plain text rendering of the outcome and SHALL return the number of bytes that rendering needs. The Zig sources SHALL pass and print bytes. They SHALL NOT read the syntax and SHALL NOT case-split on terms to produce an outcome. There SHALL NOT be a numeric result code.

#### Scenario: Identity

- GIVEN a program that binds the identity function and applies it to itself
- WHEN the Zig check runs it through `reflect_run`
- THEN the printed text is `<function>`

#### Scenario: An unbound index is reported in full

- GIVEN a term whose outcome is `unbound 2147483647`
- WHEN it is run and rendered
- THEN the printed text is `error: unbound 2147483647`, and it differs from the text for a run with no result

#### Scenario: Data comes back

- GIVEN the append program in the change's design
- WHEN the Zig check runs it
- THEN the printed text is `[1 2 3 4]`

#### Scenario: A diverging term has no result

- GIVEN a program that applies a self-applying function to itself
- WHEN the Zig check runs it with a finite budget
- THEN the printed text says there is no result within that many steps, and the call returns

#### Scenario: A malformed program is refused

- GIVEN text that is not a program
- WHEN the Zig check passes it
- THEN the printed text is a syntax error with a line and column, and nothing is run
