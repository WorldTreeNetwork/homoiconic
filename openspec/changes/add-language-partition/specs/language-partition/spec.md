## ADDED Requirements

### Requirement: Semantics live in Lean

The system SHALL implement the circular evaluator as Lean 4 source. A theorem about evaluation SHALL be a theorem about that source.

#### Scenario: One semantics language

- GIVEN the language partition
- WHEN a reader looks up where `eval` is defined
- THEN the definition is Lean 4 source

### Requirement: Zig is the host

The system SHALL run IO, allocation, and the REPL in Zig. The Zig host SHALL call the Lean kernel for evaluation. The Zig host SHALL NOT contain an evaluator.

#### Scenario: Host returns the kernel's result

- GIVEN a program accepted by the covered fragment
- WHEN the Zig host runs it
- THEN the value returned is the Lean kernel's result

#### Scenario: No second evaluator

- GIVEN the Zig source tree
- WHEN it is reviewed against this partition
- THEN it loads the Lean kernel and does not define `eval`

### Requirement: Rust is absent

The first system SHALL NOT include a Rust component.

#### Scenario: Two languages

- GIVEN the first system's build
- WHEN its implementation languages are listed
- THEN they are Lean 4 and Zig

### Requirement: Circularity is metacircular

The kernel change SHALL be accepted only when, for a named small fragment, evaluating an interpreter written as a term of the language on a program equals evaluating that program directly.

#### Scenario: Fragment equality is the kernel's job

- GIVEN this partition and no kernel yet
- WHEN someone asks what the first proof has to show
- THEN the answer is that metacircular equality, and this change does not contain the proof
