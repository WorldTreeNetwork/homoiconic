# add-event-log

> **ACTIVE BUILD, 2026-11-12.**

**Rigor:** instrument

Depends on: `add-requests`, `add-kept-state`, `add-channels` (all folded). Vision: stage 5, P13 and P14. Bead: `homoiconic-q59.27`. Authority: the user, 2026-11-12, "yes, keep going", after the report that named the event log as next.

## Why

A waiting program can be kept on disk and answered later. What it was answered with is not kept anywhere, so the state on disk is the only record: lose it and the program's history is gone, and an answer that arrives twice is taken twice. The network stages need the opposite. The list of what a machine was told is the record, the state is something that can be made again from it, and being told the same thing twice does nothing.

## What

- **A log is a list of entries.** An entry is an identifier and an answer, both data.
- **A VM is a program and the identifiers it has acted on.** It is a program run by the request driver, as before. Nothing is added to the language.
- **Handling an entry** answers the request the VM is waiting on and runs the program to its next request or its end, and records the identifier. An entry whose identifier the VM has acted on changes nothing. A VM whose program has finished is changed by no entry.
- **The state of a VM is the fold of handling over its log**, from the program's first request (`Reflect.Logged`; the executable `Reflect.vmRun` is `List.foldl`).
- **A state is kept under a root.** The kept-state session now also handles a log, and at the end saves the identifiers acted on and where the program stands as pieces under one root, a Blake3 hash.
- **A command.** `vm <store-dir> start <program-file> <log-file> [step-budget]` runs a program from its beginning and hands it a log. `vm <store-dir> from <root> <log-file> [step-budget]` hands a log to a kept state. Both print where the program stands, how many entries were given and acted on, and the root of the state.

## What is proved

For every table of operations, with no admitted step (`kernel/LogContract.lean`):

- `log_deterministic`: a program and a log lead to at most one state. `log_prefix`: the state after a log is the state after any first part of it, carried on through the rest. With `vmRun` being a fold by definition, this is P13.
- `log_again`: handling an entry that is already in the log leaves the state as it is. `log_redeliver`: an entry delivered again anywhere later changes nothing. `log_once`: a log does what its first deliveries do, in their order. This is P14.
- `log_restart`: a state reached by a first part of the log, given the whole log, reaches what the whole log reaches from the start. A machine that restarts from a kept state does not need to know how much of the log that state covers.
- `log_interact`: a VM's run is a run of its program by the request driver against the answers of the first deliveries.
- `log_machine`, `log_machine_exact`: the machine handles a log exactly as direct evaluation does. `vm_true`: a state the executable fold reports is the compiled form of the program's state with that log.

## What this shows

From `host/check.sh`:

- `examples/ask.hom` with `examples/ask.log` ends with 42 and a state root.
- Started on the first entry alone it waits on `[2, 20]`. That kept state, handed the whole log in a new process, acts on one entry of two and reaches the same root.
- With the store deleted, the log alone gives the same root.
- `examples/ask-again.log`, the same two entries delivered five times, one of them with another answer, gives the same root: 5 given, 2 acted on.
- The same two answers in the other order give another root.
- `kernel/LogCheck.lean`: the root the session saves is the root of the proved fold's state saved the same way, for logs of no, one, two and three entries, for `ask.hom` and `keep.hom`.

## Limits

- **An identifier is whatever the log says it is.** It is not a hash of the entry, it is not checked and nothing is signed. Of two different entries with one identifier, the first is acted on. Making identifiers by hashing a signed op is the host's (`identikey-log`) and comes with the network stages.
- **An entry does not say which request it answers.** It answers the one the VM is waiting on. The order of first deliveries decides the state; nothing here says a state is the same under another order (P16 is not claimed).
- **A state holds every identifier acted on.** The list grows with the log and is searched from the front.
- **A finished VM records nothing.** An entry given after the end is not remembered.
- **That a restarted state has the same root is tested, not proved.** `log_restart` says the states are equal. That equal states reached by different routes are cut into the same pieces is checked on examples.
- **The session is tested, not proved.** Each machine run in it is a turn the store theorems cover; the joining of turns over a log repeats `vmRun` and is compared with it in `LogCheck.lean`.
- **A turn that does not end within the budget keeps nothing.** No state is reported for that call.
- **The session's budget is not the fold's.** The session counts steps of the lazy machine, which takes more of them than the plain machine `vmRun` runs on. With the same number, the fold can give a state where the session gives none: `ask.hom` at 41 steps a turn does. The comparison in `LogCheck.lean` is of the states both give.
- **A kept state is checked for its shape, not all the way down.** `from` refuses a root whose piece is not exactly `[seen, status]` with a known status, a result that is data, or a waiting program that is a function. It does not walk a function's environment, which would fetch what the turn may never read. A function made by something other than saving can hold a part the machine cannot use; a turn that reaches it ends in a machine fault and keeps nothing.
- **The command is handed a log; it does not keep one.** Appending to a log, ordering it and deciding who may add to it are not here. The state does not name its program or its log.
- **One program.** A VM is not a set of processes; under `vm` the channel payloads are requests to the outside (`homoiconic-q59.26`).
- **The interpreter on data is not covered** for a log.

## Disposition

ACTIVE BUILD, 2026-11-12.
