# channels

What is built: several programs run side by side as processes and talk over channels, inside one machine. Nothing is added to the language: a process is a program that makes requests (`openspec/specs/requests/spec.md`), and four shapes of payload are channel requests. A schedule, a list of events, says what happens. A channel name in a program is a name value, a kind of data that carries a number (`openspec/specs/code-as-data/spec.md`); a new channel is answered with one, a send or receive takes one, and a number in their place is a request to the outside. A process is handed only the name values its starter or sender holds that occur in the start data or the message, so a number hands over nothing, and it holds each name once. Holding is the scheduler's list of numbers, not the value: a name value is not a key. Events and schedule files hold plain numbers. The definitions are in `kernel/Reflect/Channel.lean`, the proofs in `kernel/Reflect/ChannelProof.lean`, and the exact statements in `kernel/ChannelContract.lean`. A run spread over two machines, recorded by both and replayed here, is `openspec/specs/crossing/spec.md`; nothing in this spec is about a second machine. Names became a kind of data in `openspec/changes/archive/2026-11-17-add-data-kinds/`; before it a name was a number, and any process holding a number that occurred in quoted code or a message handed it over.

## Purpose

State what a channel request is, what an event does, what a process may use, and what is proved. This spec does not say how a schedule is chosen. Its theorems are about one machine. Two machines are `openspec/specs/crossing/spec.md`, where a name across machines is a hypothesis, not a theorem.

## Requirements

### Requirement: Channel requests are payloads

A request whose payload is `[0]` SHALL be a request for a new channel. `[1, name, message]`, with `name` a name value, SHALL be a send. `[2, name]`, with `name` a name value, SHALL be a receive. `[3, program, start]`, with `program` the data form of a program, SHALL be a request to start that program applied to the data `start` as a new process. Every other payload SHALL be a request to the outside; `[1, n, message]` and `[2, n]` with `n` a number are among them. No term, value, outcome, evaluation rule, interpreter branch or machine instruction SHALL be added for channels. The rules of `Direct` and the cases of `step` that a name has SHALL be those of a data value that carries a number, and SHALL NOT mention a channel, a send, a receive or holding.

#### Scenario: Channels add nothing to the language

- GIVEN the definitions of `Term`, `Value`, `Outcome`, `Direct`, `interp`, `step` and `Drive`
- WHEN each is read for a term, rule, branch or instruction that is there for channel scheduling
- THEN none has one: `Term`, `Value`, `Outcome`, `interp` and `Drive` are as they were before names, and what `Direct` and `step` gained is the rules and cases for text and names as data, the same whether or not a program uses a channel

#### Scenario: A start request with no program is the outside's

- GIVEN a payload `[3, d, s]` where `d` is not the data form of a program
- WHEN it is read
- THEN it is a request to the outside

#### Scenario: A number is not a name

- GIVEN `examples/number.hom`, in which the first process makes a channel and a second process, started on `[]`, asks `[2, 0]` with the number 0
- WHEN it is run with the events chosen, and again with a schedule that says the two meet
- THEN in the first run the second process is waiting on a request to the outside and no event is offered, and in the second run the meeting is refused

### Requirement: An event does one thing

A configuration SHALL be the processes, in the order they were started, each waiting on a request or finished and each holding a list of names, and the list of names made so far. A process SHALL be named by its place. An event SHALL be one of four, and SHALL be able to happen only as stated:

- Process `i` is given the new name `n`: `i` is waiting on a request for a new channel and `n` has not been made. `i` continues on the name value of `n` and holds it.
- Process `i` starts a process: `i` is waiting on a start request. The program is evaluated on the start data and becomes the last process, holding the names `i` holds that occur in the start data. `i` continues on `[]`.
- Process `i` sends to process `j`: `i` is waiting to send a message on a name, `j` is waiting to receive on the same name, and both hold it. `i` continues on `[]`. `j` continues on the message and also holds the names `i` holds that occur in the message and that `j` does not hold already.
- Process `i` is answered `a` from outside: `i` is waiting on a request to the outside. `i` continues on `a`.

A process that continues SHALL run to its next request or its end as a turn of the request driver does: a result that is not a function finishes it, every function is read as a request, and the payload must be data. A name occurs in data when it is one of the name values in it, at any depth of arrays. A number or a text SHALL NOT make a name occur. The program of a start request SHALL NOT be searched for names; the start data is. An event SHALL name a new channel by its number, and a schedule SHALL hold numbers, not name values. There SHALL be no queue: a send happens only together with a receive.

#### Scenario: Two processes exchange a name and talk over it

- GIVEN `examples/ping.hom`
- WHEN it is run with the events chosen
- THEN the schedule is `[[0, 0, 0], [1, 0], [0, 0, 1], [2, 0, 1], [2, 0, 1], [2, 1, 0]]`, process 0 finishes with 42, process 1 finishes with `[41]`, and each holds `[#1, #0]`

#### Scenario: A name already made is refused

- GIVEN `examples/ping.hom` and the schedule `[[0, 0, 3], [1, 0], [0, 0, 3]]`
- WHEN it is run
- THEN the first two events happen and the third is refused

#### Scenario: Numbers in code and messages hand over nothing

- GIVEN `examples/sieve.hom`, in which each filter is started on its own quoted code, its input and the report channel, and the numbers 2 to 30 and 0 are sent as messages
- WHEN it is run with the events chosen
- THEN process 0 finishes with `[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]`, no process after process 2 holds `#0`, and no process holds a name twice

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

A send and a receive SHALL meet only on a name both processes hold (`Step.comm_held`). After an event, a process SHALL hold a name only if it held the name before, or the event made the name for that process, or the event is a message to it, or a start, from a process that held the name (`Step.held_from`). Every name held by a process of a program SHALL have been made by an event of the schedule (`Network.held_issued`). No process of a program SHALL hold a name twice (`Network.held_nodup`). These SHALL hold for every way of evaluating, not only direct evaluation. Holding is the scheduler's list. A name value is not a key: a process can have a name value it does not hold, in its program or in an answer from outside, and cannot send or receive on it. That a program cannot come to have such a value is not claimed.

#### Scenario: A name in hand is not a name held

- GIVEN `examples/guess.hom`, in which the first process makes a channel and starts, on `[]`, a program with the name spliced into its code, and that process asks to receive on the name
- WHEN it is run with the events chosen, and again with a schedule that says the two meet
- THEN in the first run the first process waits on `[1, #0, 7]` holding `[#0]`, the second waits on `[2, #0]` holding `[]`, and no event is offered, and in the second run the meeting is refused

#### Scenario: A name is held once

- GIVEN `Network S p evs cfg` and a process of `cfg`
- WHEN `kernel/ChannelContract.lean` is checked
- THEN its list of held names has no repeat

### Requirement: The machine runs a schedule as the program does

For every operation table, a run by direct evaluation SHALL be, in compiled form, a run on the machine (`network_machine`), and every run on the machine SHALL be the compiled form of a run by direct evaluation (`network_machine_exact`). The events the executable scheduler reports as done after a given schedule (`schedRun`) or a schedule it chose (`autoRun`), and the configuration it reports, SHALL be a run of the program by direct evaluation (`replay_true`, `auto_true`), however the run stopped. An event that cannot happen SHALL be reported as refused, and a machine run that does not halt within its budget, charged as `runPriced` charges it, as unfinished; in both cases the configuration SHALL be the one before that event. How `autoRun` chooses SHALL NOT be relied on by any theorem, and no theorem SHALL be about which event it would choose next: it never offers an answer from outside, and an event it offers may not halt within the budget.

#### Scenario: The scheduler's report is true

- GIVEN `beginRun budget p = some c₀` and any schedule `evs`
- WHEN `kernel/ChannelContract.lean` is checked
- THEN there is a configuration `cfg` with `Network sourceP p (schedRun budget c₀ evs).1 cfg` and the reported configuration its compiled form

### Requirement: The interpreter on data runs a schedule as the program does

For every operation table, every program and every schedule, the schedule SHALL lead the program, by direct evaluation, to a configuration exactly when it leads the run in which every evaluation is done by the interpreter on data (`interpretedP`) to the data form of that configuration (`network_reflective`). Every run of the interpreter on data SHALL be the data form of a run by direct evaluation (`network_interpreted_exact`). In that run a program, and the program of a start request applied to its start data, SHALL be begun by `interp` on its data form, the payload and the rest of a request SHALL be evaluated by the interpreter's `evalTerm`, a finished process SHALL hold its outcome as data and a waiting process its function as data. The payloads, the events, the names held and the names made SHALL be the same in both runs. The statements SHALL have no condition on the program or the schedule. What is interpreted is evaluation: reading a payload, holding and what an event does are the scheduler's, defined once for every way of evaluating, and are not run by the interpreter. Nothing is stated for the interpreter interpreting itself to a depth beyond one, or for the interpreter run on the machine.

#### Scenario: The interpreter follows the schedule

- GIVEN a program `p`, a schedule `evs` and a configuration `cfg`
- WHEN `kernel/ChannelContract.lean` is checked
- THEN `Network sourceP p evs cfg` holds exactly when `Network interpretedP p evs (cfg.map reifyOutcome reifyValue)` does

#### Scenario: The interpreter has no other runs

- GIVEN `Network interpretedP p evs ic`
- WHEN `kernel/ChannelContract.lean` is checked
- THEN there is a configuration `cfg` with `Network sourceP p evs cfg` and `ic` its data form

### Requirement: The channel theorems depend on the logic only

`kernel/ChannelContract.lean` SHALL state each theorem for every operation table, SHALL NOT import a table, and SHALL print each theorem's axioms. The axioms SHALL be among `propext`, `Classical.choice` and `Quot.sound`.

#### Scenario: Axioms

- GIVEN the built kernel
- WHEN `lake env lean ChannelContract.lean` runs
- THEN it exits 0 and prints no axiom outside those three
