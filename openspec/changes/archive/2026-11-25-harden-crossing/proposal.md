# Harden the crossing: own budgets, a bound on what a guest holds, a root of each state

> **FOLDED** 2026-11-25 into `openspec/specs/crossing/spec.md`, `unikernel-net` and `zig-host`. Was ACTIVE BUILD, 2026-11-25. Advise read (Opus): send-back, answered in `design.md`. Beads `homoiconic-q59.79`, `homoiconic-q59.71`, `homoiconic-q59.69`. Asked by Duke, through the orchestrator, as one change.

**Rigor:** architecture (new note kinds and a ledger in `Reflect`, theorems extended, a new record form, a guest protocol change in trusted image code).

## Why

Three weaknesses of the crossing (`openspec/specs/crossing/spec.md`), found in the q59.67 and q59.72 audits:

1. **The peer chooses this guest's work** (`q59.79`). A guest with no program takes the budget of every machine run it makes from the first batch that carries one (`Surface.Cross.Guest.take`), so the peer sets how many steps each of this guest's turns may take, up to any number.
2. **Nothing bounds what a guest holds across turns** (`q59.71`). Each turn is limited to `Reflect.turnSpace` cells made, but the guest keeps every process's state, the packets it sent, the sends waiting for a receiver and its log, and nothing bounds those together. A program that keeps data over many turns, or starts processes that each keep a turn's worth, runs the 512 MiB guest out of memory: `INTERNAL PANIC`, and the guest powers off.
3. **A record is compared by lines** (`q59.69`). The check compares each process the replay ends with against the guest's line: a finished value or a payload, and the names held. What a waiting process holds is not compared, so a guest that remakes its chain and signs it can hand over a log whose replay differs from its report in a closure, and be accepted. Nor is the order in which one guest acknowledged its crossings compared with the order in which the other took them, so records of two different runs can be checked as one.

## What changes

- **Budgets are the guest's own.** Each end of a crossing has a step limit and a turn limit (the cells a turn may make), `reflect.budget=<steps>` and `reflect.turn=<cells>`, or the defaults 100000000 and 500000. Each number a guest runs with is the least of its own limit, the program frame's budget (steps, for the guest given the program) and what the peer announces before the guest has run anything; then it is fixed. The guest given the program does not begin it until it has heard the peer once, so both guests run every turn with one budget and one turn space. A peer can lower them, never raise them. The channel runs take the turn space as a parameter (every other driver keeps `Reflect.turnSpace`). The record states what was run with and the guest's own limits; the check requires the two equal, each within its record's own limits and within the check's own ceilings.
- **A guest bounds what it holds.** Each guest has a hold, `reflect.hold=<cells>` or 2000000, its own. It keeps a ledger: each entry is charged the cells its machine runs made (measured as `runSpace` measures them), the packets and programs it took or made, and a fixed amount for the entry and each new process. When an entry's charge passes what is left, the guest asks the runtime how many cells it holds (`reflect_live_cells` on the whole guest) and records the answer: `held m`, and the ledger begins again at `hold - m`, when `m` is at most three quarters of the hold; otherwise `full m`, and the guest stops: it records only the acknowledgements still owed, and closes. Two pure caps bound the record itself (60000 entries, 4096 processes) and end in `full` too. The check replays each side's ledger from the replay's states and refuses a record whose counts or `full` are not where the ledger and caps put them. The count is trusted and stated; the ledger is pure and the same on the guest and in the replay. A guest puts out at most 64 crossings at once, produces nothing while 128 of its packets are uncounted, and queues at most 128 of the peer's packets.
- **Each process line carries a digest.** A line ends with `root <hex>`, the Blake3 hash of the byte form of the process's held names and status (its function and payload, or its outcome); when the function's form is too large, `data <hex>` over the names and the data alone; `root none` only past a side's room. The replay computes the same line, so the digest is compared wherever the line is. The check also requires each guest's acknowledgements, in log order, to be exactly the other guest's takings of its crossings, in that guest's log order.
- **The record's form changes.** A record begins `form 2` and has the lines `budget <steps> <cells>` and `own <steps> <cells> <hold>`, the entries `[5, m]` (`held`) and `[6, m]` (`full`), and the digest on each process line; a batch carries two numbers. A record of the old form is refused. Payloads and results longer than 512 written are printed as `more than 512 written`; the digest still covers them.
- **Proved**, with no `sorry` and no new axiom: `accepted_network` (now for every turn space), `combine_merged`, `merged_exact` and `merged_once` with the two new entries; the check's single replay is `schedIn`'s (`traceRun_sched`); the measured machine runs are the runs (`runTurnMade_fst` and its relatives); and of the ledger walk, that between two counts a side made no more than the credit it had beyond the one entry that spent it, and that after `full` only acknowledgements follow.
- **Tested**, in one process (`kernel/CrossCheck.lean`) and on two real guests (`unikernel/check-wire.sh`), each new refusal with its reason and a control that fails with its check undone (`kernel/cross-controls.py`): a peer that announces a huge budget; a program that holds more and more across turns, one that starts processes on the peer that each hold a turn's worth, and the worst single entry, each ending `full` on the image and not in a panic (and in `INTERNAL PANIC: out of memory` with the hold set to its largest); a guest that hands over a different run of the same program, re-signed.

## What stays a hypothesis

- That a guest ran the Lean it claims to. Each guest signs only its own record. A guest that lies can still hand over a record of another run of the program, if that run agrees with the peer's record at every crossing and its lines and roots are that run's; `design.md` says exactly what it can and cannot do.
- The count. A guest's `held m` and `full m` are its runtime's count, not a function of the state; the check verifies where the counts are, not what they say.
- That the charge table covers what an entry makes in memory, and that a cell is at most 24 bytes; as in `add-space-budget`.
- Blake3 names one byte string, and the byte form names one value (D5, D7).

## Not in this change

- More than two guests: a new bead.
- A turn space of the guest's own for drivers other than the crossing (requests, the log, the node, the keep session keep `Reflect.turnSpace`).
- Mjolnir does not use the crossing and is not touched.

No new UI because this is a kernel, image and check change.
