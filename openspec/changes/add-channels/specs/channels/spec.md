# channels

What is built: several programs run side by side as processes and talk over channels, inside one machine. Nothing is added to the language: a process is a program that makes requests (`openspec/specs/requests/spec.md`), and four shapes of payload are channel requests. A schedule, a list of events, says what happens. The definitions are in `kernel/Reflect/Channel.lean`, the proofs in `kernel/Reflect/ChannelProof.lean`, and the exact statements in `kernel/ChannelContract.lean`.

## Purpose

State what a channel request is, what an event does, what a process may use, and what is proved. This spec does not say how a schedule is chosen, and nothing in it is about more than one machine.

## ADDED Requirements

### Requirement: Channel requests are payloads

A request whose payload is `[0]` SHALL be a request for a new channel. `[1, name, message]`, with `name` a number, SHALL be a send. `[2, name]`, with `name` a number, SHALL be a receive. `[3, program, start]`, with `program` the data form of a program, SHALL be a request to start that program applied to the data `start` as a new process. Every other payload SHALL be a request to the outside. No term, value, outcome, evaluation rule, interpreter branch or machine instruction SHALL be added for channels.

#### Scenario: Channels add nothing to the language

- GIVEN the definitions of `Term`, `Value`, `Outcome`, `Direct`, `interp`, `step` and `Drive`
- WHEN this change lands
- THEN none of them has changed

#### Scenario: A start request with no program is the outside's

- GIVEN a payload `[3, d, s]` where `d` is not the data form of a program
- WHEN it is read
- THEN it is a request to the outside

### Requirement: An event does one thing

A configuration SHALL be the processes, in the order they were started, each waiting on a request or finished and each holding a list of names, and the list of names made so far. A process SHALL be named by its place. An event SHALL be one of four, and SHALL be able to happen only as stated:

- Process `i` is given the new name `n`: `i` is waiting on a request for a new channel and `n` has not been made. `i` continues on `n` and holds it.
- Process `i` starts a process: `i` is waiting on a start request. The program is evaluated on the start data and becomes the last process, holding the names `i` holds that occur in the start data. `i` continues on `[]`.
- Process `i` sends to process `j`: `i` is waiting to send a message on a name, `j` is waiting to receive on the same name, and both hold it. `i` continues on `[]`. `j` continues on the message and also holds the names `i` holds that occur in the message.
- Process `i` is answered `a` from outside: `i` is waiting on a request to the outside. `i` continues on `a`.

A process that continues SHALL run to its next request or its end as a turn of the request driver does: a result that is not a function finishes it, every function is read as a request, and the payload must be data. A name occurs in data when it is one of the numbers in it. There SHALL be no queue: a send happens only together with a receive.

#### Scenario: Two processes exchange a name and talk over it

- GIVEN `examples/ping.hom`
- WHEN it is run with the events chosen
- THEN the schedule is `[[0, 0, 0], [1, 0], [0, 0, 1], [2, 0, 1], [2, 0, 1], [2, 1, 0]]`, process 0 finishes with 42, process 1 finishes with `[41]`, and each holds `[1, 0]`

#### Scenario: A name already made is refused

- GIVEN `examples/ping.hom` and the schedule `[[0, 0, 3], [1, 0], [0, 0, 3]]`
- WHEN it is run
- THEN the first two events happen and the third is refused

### Requirement: A schedule leads to one configuration

For every operation table, a program and a schedule SHALL have at most one configuration (`network_deterministic`). The names made and the answers from outside SHALL be events of the schedule, so nothing else is needed to repeat a run.

#### Scenario: Replay

- GIVEN `Network sourceP p evs a` and `Network sourceP p evs b`
- WHEN `kernel/ChannelContract.lean` is checked
- THEN `a = b`

#### Scenario: The schedule decides

- GIVEN `examples/race.hom`, in which two processes wait on one channel and one message is sent
- WHEN it is run with the events chosen, and again with `examples/race.schedule`
- THEN process 1 gets the message in the first run and process 2 in the second

### Requirement: A process uses only the names it holds

A send and a receive SHALL meet only on a name both processes hold (`Step.comm_held`). After an event, a process SHALL hold a name only if it held the name before, or the event made the name for that process, or the event is a message to it, or a start, from a process that held the name (`Step.held_from`). Every name held by a process of a program SHALL have been made by an event of the schedule (`Network.held_issued`). These SHALL hold for every way of evaluating, not only direct evaluation. A name is a number and a process can write any number; that a name cannot be guessed is not claimed.

#### Scenario: A guessed name is not usable

- GIVEN `examples/guess.hom`, in which a process started on `[]` asks to receive on the name the first process made
- WHEN it is run with the events chosen, and again with a schedule that says the two meet
- THEN in the first run both are left waiting and the second process holds nothing, and in the second run the meeting is refused

### Requirement: The machine runs a schedule as the program does

For every operation table, a run by direct evaluation SHALL be, in compiled form, a run on the machine (`network_machine`), and every run on the machine SHALL be the compiled form of a run by direct evaluation (`network_machine_exact`). The events the executable scheduler reports as done after a given schedule (`schedRun`) or a schedule it chose (`autoRun`), and the configuration it reports, SHALL be a run of the program by direct evaluation (`replay_true`, `auto_true`), however the run stopped. An event that cannot happen SHALL be reported as refused, and a machine run that does not halt within its budget as unfinished; in both cases the configuration SHALL be the one before that event. How `autoRun` chooses SHALL NOT be relied on by any theorem.

#### Scenario: The scheduler's report is true

- GIVEN `beginRun budget p = some c₀` and any schedule `evs`
- WHEN `kernel/ChannelContract.lean` is checked
- THEN there is a configuration `cfg` with `Network sourceP p (schedRun budget c₀ evs).1 cfg` and the reported configuration its compiled form

### Requirement: The channel theorems depend on the logic only

`kernel/ChannelContract.lean` SHALL state each theorem for every operation table, SHALL NOT import a table, and SHALL print each theorem's axioms. The axioms SHALL be among `propext`, `Classical.choice` and `Quot.sound`.

#### Scenario: Axioms

- GIVEN the built kernel
- WHEN `lake env lean ChannelContract.lean` runs
- THEN it exits 0 and prints no axiom outside those three
