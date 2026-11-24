# crossing delta: a run on two guests, recorded and replayed

## ADDED Requirements

### Requirement: A guest's log holds local events and halves of crossings

An entry of a guest's log SHALL be one of five (`Reflect.Entry`): `did ev`, a local event with the guest's own places; `out i k`, process `i`'s start or send put out to the peer as the guest's crossing `k`; `spawnIn k`, the peer's crossing `k` taken as a new local process; `sendIn k j`, the peer's crossing `k` taken by local receiver `j`; `ack k i`, the peer took crossing `k` and process `i` continued. A written entry SHALL be `[mark, body]` with the link mark of `openspec/specs/event-log/spec.md` and SHALL be named by `Surface.Keep.entryName`. No new record type SHALL be added for it.

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

For every operation table, when the schedule `combine a b` gives is run by `schedRun budget` from `beginRun budget p` and ends `.ran` at a configuration, that configuration SHALL be the compiled form of one `Network sourceP p` reaches by that schedule (`accepted_network`). When `combine a b` gives a schedule, the entries placed, in order, SHALL be an interleaving of `a` and `b` that keeps each whole and in order (`combine_exact`), and the schedule SHALL be the events of those entries (`combine_events`). `kernel/CrossingContract.lean` SHALL state them, SHALL print their axioms, and the axioms SHALL be among `propext`, `Classical.choice` and `Quot.sound`.

#### Scenario: Axioms

- GIVEN the built kernel
- WHEN `lake env lean CrossingContract.lean` runs
- THEN it exits 0 and prints no axiom outside those three

### Requirement: The check replays and compares

`Surface.Cross.check` SHALL read two records and a program's bytes, require that each record names the other and that the budgets agree, combine the logs, replay the schedule with that budget, and compare each process a guest reported with the process at its global place in the replay. It SHALL answer `accepted` only when all of these pass, and otherwise `refused` with the first reason. What the guests do is tested, not proved: no theorem speaks of a guest's step.

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
