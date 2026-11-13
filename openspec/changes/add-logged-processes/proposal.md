# add-logged-processes

> **ACTIVE BUILD, 2026-11-12.**

**Rigor:** instrument

Depends on: `add-channels`, `add-event-log` (both folded). Vision: stages 5 and 6; D4 (a schedule is data), P13, P14 and P17 for one machine. Bead: `homoiconic-q59.26`. Authority: the user, 2026-11-12, "hell yeah. do it", after the report that recommended this as next.

## Why

Two things were built apart. Several processes can run in one machine under a schedule, but the set of them cannot be kept: `chan` replays from the start every time. One program can be kept and driven by a log in which a repeated entry does nothing, but it is one program. A machine on a network is both at once: several processes, a record of what happened to them, and a state that can be kept, lost and made again. This change joins them.

## What

- **An op is an event with an identifier.** The events are the scheduler's four: a process is given a new name, a process starts a process, one process sends to another, a process is answered from outside.
- **A node is a set of processes and the identifiers of the ops it has acted on.** Applying an op the node has acted on changes nothing. Otherwise the event happens as `Reflect.Step` says, and the identifier is recorded. An op whose event cannot happen has no next state: a log is the record of what happened, and a list holding such an op is not the log of any run.
- **A plan.** `Reflect.plan` splits an event into the machine runs it needs and the configuration once they have ended. `Step` is proved to be exactly that, both ways.
- **A node is kept under a root.** The kept-state session now also applies a log of ops to several processes, running each event as the jobs of its plan on the lazy machine, and saves the node as pieces under one root.
- **A command.** `node <store-dir> start <program-file> <log-file> [step-budget]` runs a program as the first process and applies a log. `node <store-dir> from <root> <log-file> [step-budget]` applies a log to a kept node. Both print each process, how many ops were given and acted on, and the root.

## What is proved

For every table of operations, with no admitted step (`kernel/NodeContract.lean`):

- `node_deterministic`, `node_prefix`: a program and a log lead to at most one node, and the node after a log is the node after any first part carried on through the rest.
- `node_again`, `node_redeliver`: an op already in the log changes nothing.
- `node_restart`: a node reached by a first part of the log, given the whole log, reaches what the whole log reaches from the start.
- `node_network`: a node's processes are where the schedule of the log's first deliveries leads the program. So the channel theorems hold of a node: its processes use only names they hold, and every held name was made by an op.
- `node_machine`, `node_machine_exact`, `node_true`: the machine applies a log as direct evaluation does, and what the executable `nodeRun` reports is true however it stopped.
- `plan_step`, `step_plan`: for every way of evaluating, an event happens exactly when its plan's runs end somewhere and the plan gives the next configuration from there.

## What this shows

From `host/check.sh`:

- `examples/ping.hom` with `examples/ping.log` ends as `chan` ends it: `process 0: 42`, `process 1: [41]`, and a root.
- Stopped after three ops, both processes are waiting. That kept node, handed the whole log in a new process, applies three ops of six and reaches the same root.
- With the store deleted, the log alone gives the same root. `examples/ping-again.log`, ten deliveries of the six ops, gives it too.
- The other order of the race, written as a log, ends as `chan` ends it under `examples/race.schedule`.
- A log for `examples/guess.hom` whose third op cannot happen stops there, says so, and keeps the node the first two ops reach.
- `kernel/NodeCheck.lean`: for `ping`, `race` and `guess`, at every prefix of the chosen schedule, the root the session saves is the root of `nodeRun`'s node saved the same way, and a node kept at any prefix and given the whole log reaches the whole log's root. Nine malformed pieces are refused.

## Limits

- **The session is tested, not proved.** Whether an event can happen, what it needs run and the configuration after it are `plan`'s, which is proved to be `Step`. Running the jobs on the lazy machine, reading a payload, and joining the runs are the session's, compared with `nodeRun` on examples. That a restarted node has the same root is tested.
- **A log is handed over; nothing here chooses.** The command does not pick events or make identifiers. `chan` still chooses a schedule, which has no identifiers.
- **An op that cannot happen stops the log.** The ops after it are not applied, and the node kept is the one before it. Nothing here says such an op should be skipped or tried again later.
- **An identifier is whatever the log says**, as for a VM: not a hash, not signed, and of two ops with one identifier the first is applied.
- **A node holds every identifier acted on, and the payload of every waiting process.** Opening a kept node reads all of them, and the piece each waiting function is held in, to check that it is a function. What a function has captured is fetched only when a run looks at it.
- **A kept node is checked for its shape, not all the way down.** A function's environment is not walked. What the piece says is taken as it is: the identifiers acted on, the names made, what each process holds, what it is waiting on and what it finished with. A piece made by something other than saving can give a process a name or a payload its function would not give, and identifiers put in it stop the ops that carry them from being applied. The root names the piece; who to take a root from is the host's.
- **A step that does not end within the budget keeps nothing**, and the session's budget counts lazy steps, as for a VM.
- **One machine.** Nothing here is about two nodes. The interpreter on data is not covered.
- **The VM of `add-event-log` is unchanged.** It is one program whose entries carry answers; a node with one process answered from outside does the same work with ops `[3, 0, answer]`, and a finished node does not ignore further ops as a finished VM does: an op for a finished process cannot happen. The two are not unified here.

## Disposition

ACTIVE BUILD, 2026-11-12.
