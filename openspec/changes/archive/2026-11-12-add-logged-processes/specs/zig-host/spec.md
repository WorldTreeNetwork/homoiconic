# zig-host

## ADDED Requirements

### Requirement: A command applies a log to processes kept in a directory

The host SHALL provide a command that takes a store directory and either `start` with a program file and a log file, or `from` with a root and a log file, and an optional step budget. It SHALL pass the bytes to the Lean export `reflect_node_start` or `reflect_node_from` and SHALL then serve the session as the command that runs one turn does. A log file SHALL be a program whose result is an array of `[identifier, event]`, an event written as a schedule file writes it. The text SHALL be one line for each process, then `entries: N given, K acted on`, then a `refused:` line when an op could not happen, then `state: ` and the root, then the store line. The host SHALL NOT read the log, decide what an op does, choose an event, or name the node. It SHALL exit 0 whenever the kernel answered, 3 with one line on standard error and nothing written when the directory lacks a piece that is needed, and 2 with a message on standard error for a wrong call, a file or directory it cannot read, or a file it cannot write.

#### Scenario: Stop, restart, same node

- GIVEN `examples/ping.hom` and an empty directory
- WHEN it is started on `examples/ping-part.log`, and the root printed is then handed `examples/ping.log` in another call
- THEN the first call shows both processes waiting, the second prints `entries: 6 given, 3 acted on`, and its root is the one a start on `examples/ping.log` prints

#### Scenario: An op that cannot happen

- GIVEN `examples/guess.hom` and a log whose third op is `[3, [2, 0, 1]]`
- WHEN the command runs
- THEN it prints `entries: 4 given, 2 acted on` and `refused: [3, [2, 0, 1]] cannot happen`, exits 0, and its root is the one the first two ops alone give

#### Scenario: The wrong kind of root

- GIVEN the root of a state the `vm` command kept
- WHEN it is given to `from`
- THEN the command prints `store error: the root is not a kept node` and exits 0
