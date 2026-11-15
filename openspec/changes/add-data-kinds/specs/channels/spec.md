## MODIFIED Requirements

### Requirement: Channel requests are payloads
<!-- base: f9683e877dd64ed1d9d3c993c2d4bc7252676185 openspec/specs/channels/spec.md -->

A request whose payload is `[0]` SHALL be a request for a new channel. `[1, name, message]`, with `name` a name value, SHALL be a send. `[2, name]`, with `name` a name value, SHALL be a receive. `[3, program, start]`, with `program` the data form of a program, SHALL be a request to start that program applied to the data `start` as a new process. Every other payload SHALL be a request to the outside; `[1, n, message]` and `[2, n]` with `n` a number are among them. No term, value, outcome, evaluation rule, interpreter branch or machine instruction SHALL be added for channels.

#### Scenario: Channels add nothing to the language

- GIVEN the definitions of `Term`, `Value`, `Outcome`, `Direct`, `interp`, `step` and `Drive`
- WHEN this change lands
- THEN none of them has changed

#### Scenario: A start request with no program is the outside's

- GIVEN a payload `[3, d, s]` where `d` is not the data form of a program
- WHEN it is read
- THEN it is a request to the outside

#### Scenario: A number is not a name

- GIVEN `examples/number.hom`, in which the first process makes a channel and a second process, started on `[]`, asks `[2, 0]` with the number 0
- WHEN it is run with the events chosen, and again with a schedule that says the two meet
- THEN in the first run the second process is waiting on a request to the outside and no event is offered, and in the second run the meeting is refused

### Requirement: An event does one thing
<!-- base: f9683e877dd64ed1d9d3c993c2d4bc7252676185 openspec/specs/channels/spec.md -->

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

### Requirement: A process uses only the names it holds
<!-- base: f9683e877dd64ed1d9d3c993c2d4bc7252676185 openspec/specs/channels/spec.md -->

A send and a receive SHALL meet only on a name both processes hold (`Step.comm_held`). After an event, a process SHALL hold a name only if it held the name before, or the event made the name for that process, or the event is a message to it, or a start, from a process that held the name (`Step.held_from`). Every name held by a process of a program SHALL have been made by an event of the schedule (`Network.held_issued`). No process of a program SHALL hold a name twice (`Network.held_nodup`). These SHALL hold for every way of evaluating, not only direct evaluation. Holding is the scheduler's list. A name value is not a key: a process can have a name value it does not hold, in its program or in an answer from outside, and cannot send or receive on it. That a program cannot come to have such a value is not claimed.

#### Scenario: A name in hand is not a name held

- GIVEN `examples/guess.hom`, in which the first process makes a channel and starts, on `[]`, a program with the name spliced into its code, and that process asks to receive on the name
- WHEN it is run with the events chosen, and again with a schedule that says the two meet
- THEN in the first run the first process waits on `[1, #0, 7]` holding `[#0]`, the second waits on `[2, #0]` holding `[]`, and no event is offered, and in the second run the meeting is refused

#### Scenario: A name is held once

- GIVEN `Network S p evs cfg` and a process of `cfg`
- WHEN `kernel/ChannelContract.lean` is checked
- THEN its list of held names has no repeat
