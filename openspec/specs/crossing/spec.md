# crossing

What is built: one program run as processes spread over two network guests, each guest's own log of what it did, and a check that combines the two logs into one schedule of the one-machine network (`openspec/specs/channels/spec.md`), replays it, and compares each process with what its guest reported. The definitions of the merge are in `kernel/Reflect/Crossing.lean`, the proofs in `kernel/Reflect/CrossingProof.lean`, the exact statements in `kernel/CrossingContract.lean`, and the guest, the record and the check in `kernel/Surface/Cross.lean`. The guests that carry it are `openspec/specs/unikernel-net/spec.md`. The change is `openspec/changes/archive/2026-11-24-add-recorded-crossing/`; its design says why a crossing's event sits where the crossing was taken. `openspec/changes/archive/2026-11-25-harden-crossing/` made a guest's budgets its own, bounded what a guest holds by a ledger and a count, put a digest of each process on its line, and compared the order of acknowledgements with the order of takings; its design, D-3, says exactly what a guest that lies can still hand over. The ledger is in `kernel/Reflect/Hold.lean` and `kernel/Reflect/HoldProof.lean`.

## Purpose

State what a guest records, how two logs combine, what the check accepts, and what is proved, tested and assumed. Delivery order is an input (D4, `docs/DECISIONS.md`): it is recorded by the guest that takes, and a record replays to one configuration. This spec does not say that a guest ran the Lean it claims to, that every honest pair of logs combines (`homoiconic-q59.68`), or anything about more than two guests (`homoiconic-q59.83`).

## Requirements

### Requirement: A guest's log holds local events and halves of crossings

An entry of a guest's log SHALL be one of seven (`Reflect.Note`): `did ev`, a local event with the guest's own places; `out i k`, process `i`'s start or send put out to the peer as the guest's crossing `k`; `spawnIn k`, the peer's crossing `k` taken as a new local process; `sendIn k j`, the peer's crossing `k` taken by local receiver `j`; `ack k i`, the peer took crossing `k` and process `i` continued; `held m`, the guest counted `m` cells held when its ledger was spent and went on; `full m`, it counted `m` cells, past three quarters of its hold, and stopped. A written entry SHALL be `[mark, body]` with the link mark of `openspec/specs/event-log/spec.md` and SHALL be named by `Surface.Keep.entryName`; the bodies of the last two are `[5, m]` and `[6, m]`. No new record type SHALL be added for it.

#### Scenario: The chain is read as a log's is

- GIVEN a record whose second entry names a parent other than the first entry
- WHEN it is checked
- THEN it is refused with `does not name the entry before it`

### Requirement: Two logs combine into one schedule or are refused

`Reflect.combine a b` SHALL give a schedule of events with global places, or nothing, by the table of D-4 of the design of `add-recorded-crossing`: local events at their global places, a crossing's event at the entry that takes it, `out`, `ack`, `held` and `full` emitting nothing. It SHALL refuse a crossing taken twice, taken before it is put out, acknowledged before it is taken or by another process, a crossing number that is not the count of crossings so far, a place the guest does not have, and a log pair that ends with a crossing taken and not acknowledged. `Reflect.combineTrace` SHALL give the same schedule with the entries in the order the walk placed them; `combine` is its projection.

#### Scenario: A taken crossing repeated

- GIVEN two logs that combine, with one `sendIn` entry repeated and the chain made again
- WHEN they are checked
- THEN they are refused by the merge

### Requirement: An accepted record is a run of the one-machine network

For every operation table, when the schedule `combine a b` gives is run by `schedRun budget` from `beginRun budget p` and ends `.ran` at a configuration, that configuration SHALL be the compiled form of one `Network sourceP p` reaches by that schedule (`accepted_network`). When `combine a b` gives a schedule, the walk SHALL be one the table allows (`Merged`), and the entries placed, in order, SHALL keep `a` whole and in order and `b` whole and in order (`combine_merged`, `merged_exact`), and no crossing SHALL be taken twice (`merged_once`, `Walk.once`); the order `combineTrace` gives SHALL be such a walk (`combineTrace_walk`). The measured runs of `Reflect/Hold.lean` SHALL give, as their first part, what `runTurn`, `settleRun`, `turnRun`, `beginRun` and `stepRun` give (`runTurnMade_fst` and its relatives). Of `Hold.walk`, when it accepts a side: every stretch of entries from the start or a count up to the next count SHALL have charged, without its last entry, at most the credit it began with (`hold_stretch`); a `held m` SHALL have `m` at most the bar and begin the next stretch with the hold less `m` (`hold_count`); a `full m` SHALL be followed only by acknowledgements, at most 64 (`hold_full`); a side SHALL have at most `entryLimit + outLimit + 2` entries (`hold_entries`); and the check's replay SHALL be `schedIn` on the schedule `combine` gives when it runs every event (`traceRun_sched`). When two logs have any schedule the table allows, `combine` gives one (`combine_complete`). Two logs that are each what a guest's log allows read alone (`SideRun`), every crossing taken as the packet made for it, when they combine are accepted by `accept` and replay, at each guest's places, to that guest's processes (`replay_agrees`). `kernel/CrossingContract.lean` SHALL state them, with `runSpaceLeft_eq_within` (the measured run asks a step's charge capped by its fuel), SHALL print their axioms, and the axioms SHALL be among `propext`, `Classical.choice` and `Quot.sound`.

#### Scenario: Axioms

- GIVEN the built kernel
- WHEN `lake env lean CrossingContract.lean` runs
- THEN it exits 0 and prints no axiom outside those three

### Requirement: A guest runs its processes with the one-machine functions

`Surface.Cross.Guest` SHALL hold a guest's processes and run them with the measured runs of `Reflect/Hold.lean`, which give what `stepRun`, `turnRun`, `settleRun` and `beginRun` give, each machine run with the guest's budget (the requirement "A guest's budget is its own"). The guest given the program (`Guest.give`) is side `a`. `Guest.work` SHALL, until nothing is possible or 256 steps: work one packet from the peer; else take one pending send a local receiver can take, the oldest or with `takeNew` the newest; else do the local event `Reflect.pick` gives on the configuration with every held or stuck process hidden, naming a new channel `2 * made` on side `a` and `2 * made + 1` on side `b`; else put out the lowest process waiting to send on a name it holds. With `far` a start request is put out and not run locally. Putting out SHALL run the asker's turn on `[]` first and keep it; when that does not finish, or the packet passes 6000 bytes, nothing leaves; while 64 of the guest's crossings are not acknowledged nothing more leaves. A half that does not finish in its budget SHALL record nothing. Packets SHALL be `[0, k, program, start, held]`, `[1, k, name, message, held]` and `[2, k]` in the byte form, and a batch `[flag, got, budget, [[seq, packet], ...]]`; a packet whose `seq` is not the next expected, or that would put more than 128 packets in the guest's queues, SHALL be dropped and not counted, and taking a batch SHALL only queue. Packets the peer has counted SHALL be dropped from what the guest keeps. What a guest does is tested (`kernel/CrossCheck.lean`, `unikernel/check-wire.sh`). Of two guests that follow these functions (`Reach`, `kernel/Surface/CrossModel.lean`: a batch a guest takes is any batch the other made, taken as the data it was made from) it is proved that where nothing is in flight their logs combine (`honest_combine`), `accept` (the merge and the replay) accepts them and replays to the processes each holds (`honest_accept`), and each guest's acknowledgements are in the order of the other's takings (`honest_acks`), and that a guest that has run anything runs with the other's budgets (`honest_budget`); `kernel/GuestContract.lean` states them. Mid-run two honest logs need not combine. Not proved: that two guests that have closed have nothing in flight, that a guest that ran nothing ends with the other's budgets, that the replay's charges are the guest's, and that a batch's bytes and a record's text read back.

#### Scenario: Two guests in one process

- GIVEN `kernel/CrossCheck.lean`
- WHEN it runs
- THEN it prints only lines that start `ok`, as many as `host/check.sh` requires, and none that starts `FAIL`

### Requirement: The check replays and compares

`Surface.Cross.check` SHALL read two records of form 2 and a program's bytes, require that each record names the other, that both state the checker's `Reflect.turnSpace`, that the budgets agree and that each is at most its record's limit, combine the logs, require each guest's acknowledgements in its log's order to be the other's takings of its crossings in the other's log's order, replay the schedule with that budget, replay each side's ledger (the requirement "A guest bounds what it holds"), and compare each process a guest reported with the process at its global place in the replay. It SHALL refuse a record of another form, a mark that is not `[0, parent, order]`, and a record whose entry count or head name is not its log's. It SHALL answer `accepted` only when all of these pass, and otherwise `refused` with the first reason. The comparison is of lines: the status (a finished value or a payload, printed when at most 4096 written and as its size otherwise), the names held, and the root of the process (the requirement "A process line carries a root of the process"). A record's two names are the guests' entity names (`add-entity-keys`), and a guest signs its record's text with its entity key; `unikernel/out-net/cross-check` checks the signature, and that the key that signed is the entity the record names, before Lean sees the record. The kernel sees no signature. What is proved of two guests that follow the protocol is under "A guest runs its processes with the one-machine functions". What a guest that lies can still hand over is stated in the design of `harden-crossing`, D-3.

#### Scenario: Delivery order decides, and each order replays to its own result

- GIVEN `examples/cross-race.hom`, run on two guests with `take=old` and again with `take=new`
- WHEN each pair of records is checked
- THEN both are accepted, the two schedules differ, the first process finishes with `[1, 2]` in one and `[2, 1]` in the other, and each is what its guest reported

#### Scenario: Records of two runs

- GIVEN guest `a`'s record of the `take=old` run and guest `b`'s of the `take=new` run
- WHEN they are checked
- THEN they are refused with `the acknowledgements of b are not the order a took them in`

### Requirement: An unforgeable name across machines is a hypothesis

A crossing SHALL carry the names handed over as numbers, and the receiving guest SHALL take them as sent. That another machine cannot forge a name is a hypothesis. A record in which a guest holds a name the replay does not give it SHALL be refused when checked.

#### Scenario: A name not handed over

- GIVEN a record in which a process's reported held names include one the replay does not give it
- WHEN it is checked
- THEN it is refused at the comparison

### Requirement: A guest's budget is its own

Each guest of a crossing SHALL have a step limit of its own, given when it starts or `Cross.defaultLimit`, 100000000. The budget it runs every machine run with SHALL be the least of its limit, for side `a` the budget the program was given with, and every budget the peer's batches announced before the guest ran anything; once it has begun a program or recorded an entry, its budget SHALL NOT change. Side `a` SHALL NOT begin the program before it has taken a batch from the peer. A batch SHALL announce the sender's budget as it stands. A guest SHALL have a turn limit of its own as well, the cells a turn may make, given when it starts or `Cross.defaultTurn`, 500000, lowered the same way; every machine run of a crossing, on the guests and in the check, SHALL run with the agreed step budget and turn space (`runTurnIn`, `stepIn` and their relatives in `Reflect`; every other driver keeps `Reflect.turnSpace`). A record SHALL state what every turn ran with (`budget <steps> <cells>`) and the guest's own limits and hold (`own <steps> <cells> <hold>`).

#### Scenario: A peer announces a huge budget

- GIVEN guest `b` with limit 100000 and a batch that announces 10^18
- WHEN `b` takes it and then a start
- THEN `b` runs with its own limits and its record says `budget 100000 500000`

#### Scenario: The program comes with more than the peer allows

- GIVEN guest `a` handed a program with budget 100000 and guest `b` with step limit 50000 and turn limit 300000
- WHEN they run it and their records are checked
- THEN both records say `budget 50000 300000` and are accepted

### Requirement: A guest bounds what it holds

Each guest SHALL have a hold in cells, its own, given when it starts or `Cross.defaultHold`, 2000000,, and a credit, the hold at the start. Each entry it records but a count SHALL be charged by the table of the design of `harden-crossing`, D-2, from the cells its measured runs made and the packets and programs it took or made. When an entry's charge passes the credit, the guest SHALL count the cells it holds (the runtime's count, `reflect_live_cells` on the whole guest) and record the count at once: `held m` with the credit then the hold less `m` when `m` is at most three quarters of the hold, and `full m` otherwise. An entry that brings the side's log to 60000 entries or its processes to 4096 SHALL be followed at once by `full m`. Nothing SHALL be charged after `full`. A guest SHALL put out at most 64 crossings not yet acknowledged, produce no packet while 128 of its packets are not counted by the peer, and accept at most 128 of the peer's packets into its queues. A full guest SHALL record nothing more but the acknowledgements of crossings the peer took, SHALL drop the peer's starts and sends, and SHALL close as any guest does. The check SHALL charge each entry from the replay's states and refuse a record in which an entry passes the credit or reaches a cap and is not followed by a count, a count follows no such entry, a `held` is past three quarters of the hold or follows a cap, a `full` is within it with no cap reached, or anything but at most 64 acknowledgements follows `full`. The count is the runtime's and is not verified; the ledger and the caps are.

#### Scenario: A program that holds more and more

- GIVEN `examples/cross-grow-forever.hom`, whose first process keeps a thousand more numbers on every turn without end, run on two guests with the default hold
- WHEN the records are checked
- THEN guest `a`'s record has a `full` entry, the check accepts it and says `full a`, and no guest ended in a panic

### Requirement: A process line carries a root of the process

A process line in a record and in the replay SHALL be `<status>; holds <names>; <digest>`: the payload or result when it is at most 512 written and `more than 512 written` otherwise, the names held when there are at most 32 and their number otherwise, and `root <hex>`, the Blake3 hash of the byte form of `[names held, status]` with the status in the data form of machine values (`[0, function, payload]`, `[1, value]`, `[2, i]`, `[3]`), when that form fits in 4000000 units of `Wire.valuesFit`; otherwise `data <hex>`, the same hash with the function left out, when that fits in what is left of the side's 64000000 units; otherwise `root none`. A side's room is used in local order, a process using what it used, or 4000000 if its root did not fit.

#### Scenario: A different run of the same program, re-signed

- GIVEN a record of `examples/cross-hidden.hom` with its two local deliveries swapped, its chain made again and signed, and its lines as the guest reported them
- WHEN it is checked
- THEN it is refused at the comparison, the roots differing where the lines do not
