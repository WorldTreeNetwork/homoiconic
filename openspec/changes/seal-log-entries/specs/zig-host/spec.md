# zig-host

## MODIFIED Requirements

### Requirement: A command runs a program against a log with its state in a directory
<!-- base: 06289ae62e478a859fde3b592bcdeb76796131d5 openspec/specs/zig-host/spec.md -->

The host SHALL provide a command that takes a store directory and either `start` with a program file and a log file, or `from` with a root and a log file, and an optional step budget. It SHALL pass the bytes to the Lean export `reflect_vm_start` or `reflect_vm_from`, and SHALL then serve the session exactly as the command that runs one turn does: read the file named by each piece the kernel asks for, write each piece the kernel hands back under the name the kernel gives before printing, and print the kernel's text and a newline. A log file SHALL be a program whose result is an array of `[mark, answer]`; the kernel names each entry by the hash of the pair. The text SHALL be where the program stands, then `entries: N given, K acted on`, then `state: ` and the root, then the store line. The host SHALL NOT read the log, hash or compare an entry, decide what an entry does, or name the state. It SHALL exit 0 whenever the kernel answered, 3 with one line on standard error and nothing written when the directory lacks a piece that is needed, and 2 with a message on standard error for a wrong call, a file or directory it cannot read, or a file it cannot write.

#### Scenario: Stop, restart, same state

- GIVEN `examples/ask.hom` and an empty directory
- WHEN it is started on `examples/ask-one.log`, and the state printed is then handed `examples/ask.log` in another call
- THEN the first call prints `waiting on [2, 20]`, the second prints `42` and `entries: 2 given, 1 acted on`, and its state is the one a start on `examples/ask.log` prints

#### Scenario: The store is lost

- GIVEN the state a start on `examples/ask.log` printed
- WHEN the directory is emptied and the start is run again
- THEN it prints the same state

#### Scenario: A root that is not a state

- GIVEN the name of a stored piece that is not a VM state
- WHEN it is given to `from`
- THEN the command prints `store error: the root is not a kept state` and exits 0

#### Scenario: A log that is not a log

- GIVEN `examples/ask.answers` as the log file
- WHEN the command runs
- THEN it prints `log: entry 0 is not a mark and an answer` and exits 0

### Requirement: A command applies a log to processes kept in a directory
<!-- base: 06289ae62e478a859fde3b592bcdeb76796131d5 openspec/specs/zig-host/spec.md -->

The host SHALL provide a command that takes a store directory and either `start` with a program file and a log file, or `from` with a root and a log file, and an optional step budget. It SHALL pass the bytes to the Lean export `reflect_node_start` or `reflect_node_from` and SHALL then serve the session as the command that runs one turn does. A log file SHALL be a program whose result is an array of `[mark, event]`, an event written as a schedule file writes it; the kernel names each op by the hash of the pair. The text SHALL be one line for each process, then `entries: N given, K acted on`, then the line `refused: entry K, <event>, cannot happen` when the op at place K of the log, counted from 0, could not happen, then `state: ` and the root, then the store line. The host SHALL NOT read the log, hash or compare an op, decide what an op does, choose an event, or name the node. It SHALL exit 0 whenever the kernel answered, 3 with one line on standard error and nothing written when the directory lacks a piece that is needed, and 2 with a message on standard error for a wrong call, a file or directory it cannot read, or a file it cannot write.

#### Scenario: Stop, restart, same node

- GIVEN `examples/ping.hom` and an empty directory
- WHEN it is started on `examples/ping-part.log`, and the root printed is then handed `examples/ping.log` in another call
- THEN the first call shows both processes waiting, the second prints `entries: 6 given, 3 acted on`, and its root is the one a start on `examples/ping.log` prints

#### Scenario: An op that cannot happen

- GIVEN `examples/guess.hom` and a log whose third op is `[3, [2, 0, 1]]`
- WHEN the command runs
- THEN it prints `entries: 4 given, 2 acted on` and `refused: entry 2, [2, 0, 1], cannot happen`, exits 0, and its root is the one the first two ops alone give

#### Scenario: The wrong kind of root

- GIVEN the root of a state the `vm` command kept
- WHEN it is given to `from`
- THEN the command prints `store error: the root is not a kept node` and exits 0
