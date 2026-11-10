# language-partition

What is built: Lean 4 owns evaluation semantics, Zig is the host and contains no evaluator, and Rust is absent. The interpreter theorem is in `openspec/specs/code-as-data/spec.md`.

## Purpose

Name the first system's language split. This spec does not contain the Lean kernel or the Zig host.

## Requirements

### Requirement: Semantics live in Lean

The system SHALL implement the circular evaluator as Lean 4 source. A theorem about evaluation SHALL be a theorem about that source.

#### Scenario: One semantics language

- GIVEN the language partition
- WHEN a reader looks up where `eval` is defined
- THEN the definition is Lean 4 source

### Requirement: Zig is the host

The system SHALL run IO, allocation, and the REPL in Zig. The Zig host SHALL call the Lean kernel for evaluation. The Zig host SHALL NOT contain an evaluator.

#### Scenario: Host returns the kernel's result

- GIVEN a program the kernel reads
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

The kernel SHALL prove that evaluating an interpreter written as a term of the language on a program equals evaluating that program directly. The statement SHALL cover every program of the language, not a fragment. The theorem and its exact statement are in `openspec/specs/code-as-data/spec.md`.

#### Scenario: The interpreter theorem is the kernel's

- GIVEN this partition
- WHEN someone asks what makes the language circular
- THEN the answer is the theorem `reflective`, proved in Lean about the evaluator that runs
