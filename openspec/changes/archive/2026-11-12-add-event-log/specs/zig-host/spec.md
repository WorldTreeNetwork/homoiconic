# zig-host

## ADDED Requirements

### Requirement: A command runs a program against a log with its state in a directory

The host SHALL provide a command that takes a store directory and either `start` with a program file and a log file, or `from` with a root and a log file, and an optional step budget. It SHALL pass the bytes to the Lean export `reflect_vm_start` or `reflect_vm_from`, and SHALL then serve the session exactly as the command that runs one turn does: read the file named by each piece the kernel asks for, write each piece the kernel hands back under the name the kernel gives before printing, and print the kernel's text and a newline. A log file SHALL be a program whose result is an array of `[identifier, answer]`. The text SHALL be where the program stands, then `entries: N given, K acted on`, then `state: ` and the root, then the store line. The host SHALL NOT read the log, decide what an entry does, or name the state. It SHALL exit 0 whenever the kernel answered, 3 with one line on standard error and nothing written when the directory lacks a piece that is needed, and 2 with a message on standard error for a wrong call, a file or directory it cannot read, or a file it cannot write.

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
- THEN it prints `log: entry 0 is not an identifier and an answer` and exits 0
