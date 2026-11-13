# event-log

What is built: a program run by the request driver, together with the identifiers of the log entries it has acted on, is a VM, and its state is the fold of a handler over its log. The definitions are in `kernel/Reflect/Log.lean`, the proofs in `kernel/Reflect/LogProof.lean`, and the exact statements in `kernel/LogContract.lean`.

## Purpose

State what a log entry does to a VM and what is proved about the state a log leads to. This spec does not say where an identifier comes from, who may add to a log, or how a log is stored.

## ADDED Requirements

### Requirement: An entry is an identifier and an answer

A log SHALL be a list of entries, and an entry SHALL be an identifier and an answer, both data. A VM SHALL be where a program run by the request driver stands, waiting on a request or finished, together with the identifiers of the entries it has acted on. Handling an entry SHALL do one of three things (`Reflect.Handle`). When the VM has acted on the entry's identifier, the VM SHALL be unchanged. When the program has finished, the VM SHALL be unchanged and the identifier SHALL NOT be recorded. Otherwise the request the VM is waiting on SHALL be answered with the entry's answer, the program SHALL run to its next request or its end, and the identifier SHALL be recorded. An evaluation that never finishes SHALL give no next state. No term, value, outcome, evaluation rule or machine instruction SHALL be added.

#### Scenario: Two entries

- GIVEN `examples/ask.hom` and the log `[[1, 20], [2, 22]]`
- WHEN the VM handles the log from the start
- THEN it acts on both entries and finishes with 42

#### Scenario: An entry after the end

- GIVEN `examples/append.hom`, which asks nothing, and the same log
- WHEN the VM handles the log
- THEN it finishes with `[1, 2, 3, 4]` and has acted on no entry

### Requirement: The state of a VM is a fold over its log

For every operation table, a program and a log SHALL lead to at most one state (`log_deterministic`). The state after a log SHALL be the state after any first part of it, carried on through the rest (`log_prefix`). The executable VM `vmRun budget p log` SHALL be `log.foldl (handleRun budget) (bootRun budget p)` by definition.

#### Scenario: Replay

- GIVEN `Logged sourceP p log a` and `Logged sourceP p log b`
- WHEN `kernel/LogContract.lean` is checked
- THEN `a = b`

#### Scenario: A prefix

- GIVEN any program and logs `l₁` and `l₂`
- WHEN `kernel/LogContract.lean` is checked
- THEN `Logged sourceP p (l₁ ++ l₂) v ↔ ∃ s, Logged sourceP p l₁ s ∧ Replay source s l₂ v` holds

### Requirement: An entry already in the log changes nothing

For every operation table, handling an entry that is in the log a state was reached by SHALL leave that state as it is, and SHALL lead nowhere else (`log_again`). A log with an entry of its first part delivered again later SHALL lead to the states the log without that delivery leads to (`log_redeliver`). A log SHALL lead to the states its first deliveries, in their order, lead to (`log_once`, with `firsts`). Two entries SHALL be the same delivery when their identifiers are equal, whatever their answers.

#### Scenario: Delivered again

- GIVEN `examples/ask.hom` and `examples/ask-again.log`, which holds five entries with two identifiers, one of the repeats carrying another answer
- WHEN the VM handles the log
- THEN it acts on two entries and its state has the root that `examples/ask.log` gives

#### Scenario: The statement

- GIVEN `Logged sourceP p log v` and `e ∈ log`
- WHEN `kernel/LogContract.lean` is checked
- THEN `Handle source v e v' ↔ v' = v` holds

### Requirement: A state given its whole log reaches what the log reaches

For every operation table, a state reached by a first part of a log, handling the whole log, SHALL reach exactly the states the whole log reaches from the start (`log_restart`).

#### Scenario: Restart

- GIVEN `Logged sourceP p l₁ s`
- WHEN `kernel/LogContract.lean` is checked
- THEN `Replay source s (l₁ ++ l₂) v ↔ Logged sourceP p (l₁ ++ l₂) v` holds

### Requirement: A VM's run is a run of its program

For every operation table, where a VM stands after a log SHALL be how the request driver ends when the program is run against the answers of the log's first deliveries, in their order (`log_interact`).

#### Scenario: The driver agrees

- GIVEN `Logged sourceP p log v`
- WHEN `kernel/LogContract.lean` is checked
- THEN there are requests `asked` with `Interact p ((firsts [] log).map (·.answer)) asked v.status.ending`

### Requirement: The machine handles a log as the program does

For every operation table and every program, the state the machine reaches by a log SHALL be the compiled form of the state direct evaluation reaches (`log_machine`, `log_machine_exact`). A state the executable `vmRun` reports SHALL be the compiled form of the program's state with that log (`vm_true`). `vmRun` SHALL give a fresh step budget to each machine run, and SHALL report no state when a run does not halt within its budget, which claims nothing.

#### Scenario: The fold's report is true

- GIVEN `vmRun budget p log = some w`
- WHEN `kernel/LogContract.lean` is checked
- THEN there is a state `v` with `Logged sourceP p log v` and `w` its compiled form

### Requirement: A VM's state is kept under a root

`Surface.Keep` SHALL run a VM over a log against a store it is handed piece by piece: from a program's source (`vmStart`), or from the root of a kept state (`vmFrom`). When the log is handled it SHALL save the state as the piece `[seen, status]`, where `seen` is the identifiers acted on, newest first, and `status` is `[0, function]` for a waiting program, `[1, data]` for a result, `[2, i]` for the error of an unbound variable and `[3]` for the error `wrong`, cut and named as a waiting program is. It SHALL report where the program stands, how many entries were given and how many acted on, and the root. A root that does not name such a piece SHALL be refused as text. A turn that does not end within its budget SHALL save nothing. The session SHALL be compared with `vmRun` by `kernel/LogCheck.lean`: for each log tried, the root the session saves SHALL be the root of the fold's state saved the same way, and a kept state restarted on the whole log SHALL have the root the whole log gives from the start. This is tested, not proved.

#### Scenario: The session and the fold agree

- GIVEN `examples/ask.hom` and `examples/keep.hom`, and logs of no, one, two and three entries
- WHEN `kernel/LogCheck.lean` runs
- THEN every line starts with `ok`

### Requirement: The log theorems depend on the logic only

`kernel/LogContract.lean` SHALL state each theorem for every operation table, SHALL NOT import a table, and SHALL print each theorem's axioms. The axioms SHALL be among `propext`, `Classical.choice` and `Quot.sound`.

#### Scenario: Axioms

- GIVEN the built kernel
- WHEN `lake env lean LogContract.lean` runs
- THEN it exits 0 and prints no axiom outside those three
