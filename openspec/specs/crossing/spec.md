# crossing

What is built: one program run as processes spread over two network guests, each guest's own log of what it did, and a check that combines the two logs into one schedule of the one-machine network (`openspec/specs/channels/spec.md`), replays it, and compares each process with what its guest reported. The definitions of the merge are in `kernel/Reflect/Crossing.lean`, the proofs in `kernel/Reflect/CrossingProof.lean`, the exact statements in `kernel/CrossingContract.lean`, and the guest, the record and the check in `kernel/Surface/Cross.lean`. The guests that carry it are `openspec/specs/unikernel-net/spec.md`. The change is `openspec/changes/archive/2026-11-24-add-recorded-crossing/`; its design says why a crossing's event sits where the crossing was taken.

## Purpose

State what a guest records, how two logs combine, what the check accepts, and what is proved, tested and assumed. Delivery order is an input (D4, `docs/DECISIONS.md`): it is recorded by the guest that takes, and a record replays to one configuration. This spec does not say that a guest ran the Lean it claims to, that every honest pair of logs combines (`homoiconic-q59.68`), or anything about more than two guests (`homoiconic-q59.69`).

## Requirements

### Requirement: A guest's log holds local events and halves of crossings

An entry of a guest's log SHALL be one of five (`Reflect.Note`): `did ev`, a local event with the guest's own places; `out i k`, process `i`'s start or send put out to the peer as the guest's crossing `k`; `spawnIn k`, the peer's crossing `k` taken as a new local process; `sendIn k j`, the peer's crossing `k` taken by local receiver `j`; `ack k i`, the peer took crossing `k` and process `i` continued. A written entry SHALL be `[mark, body]` with the link mark of `openspec/specs/event-log/spec.md` and SHALL be named by `Surface.Keep.entryName`. No new record type SHALL be added for it.

#### Scenario: The chain is read as a log's is

- GIVEN a record whose second entry names a parent other than the first entry
- WHEN it is checked
- THEN it is refused with `does not name the entry before it`

### Requirement: Two logs combine into one schedule or are refused

`Reflect.combine a b` SHALL give a schedule of events with global places, or nothing, by the table of D-4 of the change's design: local events at their global places, a crossing's event at the entry that takes it, `out` and `ack` emitting nothing. It SHALL refuse a crossing taken twice, taken before it is put out, acknowledged before it is taken or by another process, a crossing number that is not the count of crossings so far, a place the guest does not have, and a log pair that ends with a crossing taken and not acknowledged.

#### Scenario: A taken crossing repeated

- GIVEN two logs that combine, with one `sendIn` entry repeated and the chain made again
- WHEN they are checked
- THEN they are refused by the merge

### Requirement: An accepted record is a run of the one-machine network

For every operation table, when the schedule `combine a b` gives is run by `schedRun budget` from `beginRun budget p` and ends `.ran` at a configuration, that configuration SHALL be the compiled form of one `Network sourceP p` reaches by that schedule (`accepted_network`). When `combine a b` gives a schedule, the walk SHALL be one the table allows (`Merged`), and the entries placed, in order, SHALL keep `a` whole and in order and `b` whole and in order (`combine_merged`, `merged_exact`), and no crossing SHALL be taken twice (`merged_once`, `Walk.once`). That the walk finds a schedule whenever the table allows one is not proved. `kernel/CrossingContract.lean` SHALL state them, SHALL print their axioms, and the axioms SHALL be among `propext`, `Classical.choice` and `Quot.sound`.

#### Scenario: Axioms

- GIVEN the built kernel
- WHEN `lake env lean CrossingContract.lean` runs
- THEN it exits 0 and prints no axiom outside those three

### Requirement: A guest runs its processes with the one-machine functions

`Surface.Cross.Guest` SHALL hold a guest's processes and run them with `stepRun`, `turnRun`, `settleRun` and `runPriced`, each machine run with the guest's budget. The guest given the program (`Guest.give`) is side `a`; the other takes its budget from the first batch that carries one. `Guest.work` SHALL, until nothing is possible or 256 steps: work one packet from the peer; else take one pending send a local receiver can take, the oldest or with `takeNew` the newest; else do the local event `Reflect.pick` gives on the configuration with every held or stuck process hidden, naming a new channel `2 * made` on side `a` and `2 * made + 1` on side `b`; else put out the lowest process waiting to send on a name it holds. With `far` a start request is put out and not run locally. Putting out SHALL run the asker's turn on `[]` first and keep it; when that does not finish, or the packet passes 6000 bytes, nothing leaves. A half that does not finish in its budget SHALL record nothing. Packets SHALL be `[0, k, program, start, held]`, `[1, k, name, message, held]` and `[2, k]` in the byte form, and a batch `[flag, got, budget, [[seq, packet], ...]]`; a packet whose `seq` is not the next expected SHALL be dropped, and taking a batch SHALL only queue. What a guest does is tested (`kernel/CrossCheck.lean`, `unikernel/check-wire.sh`), not proved; none of its choices is relied on by a theorem.

#### Scenario: Two guests in one process

- GIVEN `kernel/CrossCheck.lean`
- WHEN it runs
- THEN it prints 48 lines that start `ok` and none that starts `FAIL`

### Requirement: The check replays and compares

`Surface.Cross.check` SHALL read two records and a program's bytes, require that each record names the other and that the budgets agree, combine the logs, replay the schedule with that budget, and compare each process a guest reported with the process at its global place in the replay. It SHALL refuse a mark that is not `[0, parent, order]`, and a record whose entry count or head name is not its log's. It SHALL answer `accepted` only when all of these pass, and otherwise `refused` with the first reason. The comparison is of lines: a finished value, or a payload, and the names held; what a waiting process does next is not compared, and the order of one guest's acknowledgements is not compared with the order of the other's takings. A record's two names are the guests' entity names (`add-entity-keys`), and a guest signs its record's text with its entity key; `unikernel/out-net/cross-check` checks the signature, and that the key that signed is the entity the record names, before Lean sees the record. The kernel sees no signature. What the guests do is tested, not proved: no theorem speaks of a guest's step.

#### Scenario: Delivery order decides, and each order replays to its own result

- GIVEN `examples/cross-race.hom`, run on two guests with `take=old` and again with `take=new`
- WHEN each pair of records is checked
- THEN both are accepted, the two schedules differ, the first process finishes with `[1, 2]` in one and `[2, 1]` in the other, and each is what its guest reported

### Requirement: An unforgeable name across machines is a hypothesis

A crossing SHALL carry the names handed over as numbers, and the receiving guest SHALL take them as sent. That another machine cannot forge a name is a hypothesis. A record in which a guest holds a name the replay does not give it SHALL be refused when checked.

#### Scenario: A name not handed over

- GIVEN a record in which a process's reported held names include one the replay does not give it
- WHEN it is checked
- THEN it is refused at the comparison
