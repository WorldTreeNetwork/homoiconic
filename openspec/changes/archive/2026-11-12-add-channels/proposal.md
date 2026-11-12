# add-channels

> **FOLDED 2026-11-12** into `openspec/specs/channels/spec.md`, `openspec/specs/zig-host/spec.md` and `openspec/specs/state-store/spec.md`. Archived.

**Rigor:** instrument

Depends on: `add-requests` (folded). Vision: D10 (channels are requests), P12, and P17 for one machine. Bead: `homoiconic-q59.13`. Also closes `homoiconic-1e7`. Authority: the user, 2026-11-12, "go for it", after the report that named this node as next.

## Why

A program can ask the outside and continue from the answer. It cannot yet talk to another program. The network stages need programs that run side by side, pass messages, and pass the right to pass messages. This change does that inside one machine, where the order of events is a list and everything can be proved.

## What

- **Four payloads are channel requests.** `[0]` makes a channel and is answered with its name, a number. `[1, name, message]` sends. `[2, name]` receives. `[3, program, start]` starts a quoted program on the data `start` as a new process. Every other payload is a request to the outside, as before. The language gains nothing: these are payloads of `ask`.
- **A send and a receive meet.** There is no queue. A sender waits until a receiver on the same name is chosen with it, and both continue.
- **A schedule says what happens.** A schedule is a list of events: process `i` is given the new name `n`; process `i` starts a process; process `i` sends to process `j`; process `i` is answered `a` from outside. `Reflect.Step` says what each event does and when it can happen. New names and outside answers are in the schedule, so the schedule is the whole record.
- **A process holds names.** It holds a name it made, a name its starter held that occurs in the data it was started on, and a name its sender held that occurs in a message it received. A send or a receive on a name the process does not hold cannot happen.
- **The scheduler runs on the machine.** `stepRun` tries one event, `schedRun` a given schedule, and `autoRun` chooses events itself: the first process, in order, whose request has what it needs. It never offers an answer from outside, and an event it offers may still not halt within the budget. Choosing is a convenience for making a schedule. It is not fair and no theorem depends on how it chooses.
- **A command.** `chan <program-file> [schedule-file | -] [step-budget] [event-limit]` runs a program as the first process and prints the schedule it went through, each process, and how the run stopped. Given that schedule back, it runs the same events and prints the same schedule and process lines.
- **Two stale spec lines are corrected** (`homoiconic-1e7`): which exports evaluate, and where references are made.

## What is proved

For every table of operations, with no admitted step (`kernel/ChannelContract.lean`):

- `network_deterministic`: the configuration a program reaches is fixed by the program and the schedule. This is P17 for one machine.
- `Step.comm_held`: a send and a receive meet only on a name both processes hold.
- `Step.held_from`: after an event, a process holds a name only if it held it before, or the event made it for that process, or the event is a message to it, or a start, from a process that held it.
- `Network.held_issued`: every name any process holds was made by an event of the schedule. These three are P12 for channel names.
- `network_machine`, `network_machine_exact`: the machine runs a schedule exactly as direct evaluation does.
- `replay_true`, `auto_true`: the events the executable scheduler reports as done, and the configuration it reports, are a run of the program by direct evaluation. This holds when the run was refused or ran out of budget part way.

## What this shows

From `host/check.sh`:

- `examples/ping.hom`: the first process makes a channel, starts a second process on it, makes a second channel, sends that name over the first, and the two then talk over the second. It ends `process 0: 42` and `process 1: [41]`, and both hold both names.
- The schedule line of that run, saved to a file and given back, prints the same text. After a refusal or a run out of budget the printed schedule replays to the same process lines but not the same last line: the event that failed is not in it.
- `examples/race.hom`: two processes wait on one channel and one message is sent. With the chosen schedule process 1 gets it. With `examples/race.schedule` process 2 gets it, and the channel is named 5.
- `examples/guess.hom`: a process started on `[]` asks to receive on 0, the name the first process made. It holds nothing, so nothing is chosen, and a schedule that says the two meet is refused.

## Limits

- **A name is a number.** A process can write any number. What it cannot do is use a name it does not hold. Holding is kept by the scheduler, not by the name being hard to guess. D10 says a name will be an identikey key; that comes with the network stages.
- **A message hands over every held name whose number occurs in it**, whether or not the sender meant the number as a name. A sender that holds channel 3 and sends the count 3 hands over channel 3. This cannot give a process a name its sender did not hold.
- **Handing over copies.** The giver keeps the name, and a process may hold a name twice. Numbers inside quoted data in a message or in start data count as occurrences.
- **The last line of the command's text is not covered by a theorem.** `no event is offered` and `an event is offered` say what the chooser would pick. The theorems cover the events that happened and the configuration they led to.
- **A send waits for both sides.** The sender and the receiver each run to their next request inside the one event; if either does not halt in the budget, the event is unfinished and nothing changes.
- **A message is data.** A function cannot be sent. A quoted program can, and so can a name.
- **The payload numbers are taken.** Under `chan`, `examples/ask.hom`'s second request `[2, 20]` reads as a receive on 20. Under `ask`, payloads mean what they did.
- **Nothing is proved about a particular program**: not that it finishes, not that it never waits forever.
- **The interpreter on data is not covered.** The request theorems say the interpreter asks what the program asks; the same statement for a schedule of processes is not made here.
- **A set of processes is not kept on disk.** `keep` holds one waiting program.
- **A started program is run on its start data at once.** Starting costs one machine run for the child and one for the parent within the same event; if either does not halt in the budget, the event is reported unfinished and nothing changes.

## Disposition

ACTIVE BUILD, 2026-11-12. Folded and archived, 2026-11-12.
