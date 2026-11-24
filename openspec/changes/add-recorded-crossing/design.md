# Design: a recorded crossing

## The shape

One program runs as processes spread over two guests, `a` and `b`. Guest `a` is given the program and starts it as its first process; guest `b` starts with none. The claim to check is that what the two guests did, taken together, is one run of `Reflect.Network` (`kernel/Reflect/Channel.lean`): one list of processes, one schedule.

Two events of the one-machine network involve two processes: a start (`Step.spawn`: the starter continues and the child begins) and a meeting (`Step.comm`: the sender continues and the receiver takes the message). Either can have its two processes on different guests. That is a *crossing*. Every other event is local to one guest.

## D-1. What each guest records

A guest's log is a list of entries, each one of five (`Reflect.Entry`):

| Entry | Meaning | Machine run on this guest |
|---|---|---|
| `did ev` | The local event `ev` happened; places are this guest's own. | as `stepRun` |
| `out i k` | Process `i`'s request (a start or a send) was put out to the peer as this guest's crossing number `k`. `i` is held: no local event touches it until the acknowledgement. | none |
| `spawnIn k` | The peer's crossing `k`, a start, was taken: the child began here as this guest's next process. | the child's start, `runPriced budget` then `settleRun budget` |
| `sendIn k j` | The peer's crossing `k`, a send, was taken: local process `j`, waiting to receive on that name and holding it, took the message. | `turnRun budget` of `j` on the message |
| `ack k i` | The peer took this guest's crossing `k`; process `i` continued on `[]`. | `turnRun budget` of `i` on `[]` |

`k` counts a guest's own crossings from 0, so `out i k` is the `k`th `out` of its log. A crossing goes `out` on one guest, `spawnIn` or `sendIn` on the other, `ack` on the first. The request stays a rendezvous: the one who asked does not continue until the other side has taken it, as on one machine a send does not continue without a receive.

Written, an entry is `[mark, body]` with the existing link mark `[0, parent, order]` (`Reflect.readLink`), and its identifier is `Surface.Keep.entryName` of the pair, as for a VM's and a node's log. `Surface.Keep.acceptMark` reads the chain. No new record type: the body is new, the sealing and the link are the ones in place. Bodies: `[0, event]`, `[1, i, k]`, `[2, k]`, `[3, k, j]`, `[4, k, i]`.

A guest's record is its name, its peer's name, the budget, its log, and one line for each of its processes at the end (finished with what, or waiting on which payload, and the names held). The names are data to Lean. They are the entity key's public-name form once `add-entity-keys` (`homoiconic-q59.49`) lands; the signature over the record is checked by the host, as for a VM's log (`host/sig.zig`), and the kernel never sees it.

## D-2. What crosses

Packets are data in the byte form (`Wire.write`), made and read by Lean:

- `[0, k, program, start, held]`: a start. `program` and `start` are the two data of the start request `[3, program, start]`, unchanged; `held` is `grant held start`, the names the starter holds that occur in the start data.
- `[1, k, name, message, held]`: a send on `name`. `held` is `grant held message`.
- `[2, k]`: the peer's crossing `k` was taken.

Any quoted program can cross, with any start data: nothing is compiled in. The child is a process of the receiving guest like any other; that guest's scheduler runs it to its end, or as far as the budget of each of its turns lets it.

Transport: the guest with `reflect.peer` is the QUIC client, the one with `reflect.wire_port` the server, as now. One exchange is one connection: the client's stream carries a batch, the server's answer carries a batch. A batch is `[flag, got, [[seq, packet], ...]]`. Each guest numbers the packets it sends; `got` is how many of the peer's it has accepted, in order. A packet whose `seq` is not the next expected is dropped, and a guest sends again what the peer has not counted. So a lost or repeated exchange changes nothing. `flag` is 0 while the sender has work to do, 1 when it is idle, 2 when the client has seen both idle with nothing in flight and closes. Batching, numbering and the flag are Lean's (`Surface.Cross`); Zig opens connections and moves the bytes.

## D-3. What a guest chooses, and the knobs

The local scheduler is `Reflect.pick` over the processes not held. Three choices are the guest's and are not fixed by the semantics; each is recorded by the entry it produces:

- *Where a start goes.* `reflect.spawn=far` puts every start request of this guest out to the peer; without it a start is local.
- *When a send is put out.* When no local event is possible, a process waiting to send on a name it holds is put out to the peer, one at a time, lowest place first. Once out it is held, even if a local receiver appears later.
- *Which pending send is taken first.* When several of the peer's sends could be taken by local receivers, `reflect.take=old` (default) takes the lowest `k`, `reflect.take=new` the highest. This is the forced ordering the check uses: with two senders on `b` and one receiver on `a` that receives twice, the two settings record the two delivery orders.

A guest takes in before it does local events, and does local events before it puts a send out. None of this is relied on by a theorem. Like `autoRun`'s choice, it can leave a program stuck that another schedule would finish.

Names: guest `a` makes even names and `b` odd, so the two never make one name. The merge does not rely on it: a name made twice is refused by the replay (`Step.fresh`).

## D-4. How two logs combine

`Reflect.combine (a b : List Entry) : Option (List Event)` walks the two logs with one pointer each. Its state (`Mix`) is the global place of each local place of each guest, the number of processes so far, and for each guest its crossings so far, each with the global place of the process that asked and one of `offered`, `taken`, `acked`. At the start `a`'s place 0 is global place 0. An entry of guest `s` is placed like this:

| Entry | Needs | Event emitted | State after |
|---|---|---|---|
| `did (fresh i n)`, `did (comm i j)`, `did (answer i x)` | `i`, `j` are local places | the event at their global places | unchanged |
| `did (spawn i)` | `i` local | `spawn g(i)` | `s`'s next local place is the next global place |
| `out i k` | `i` local; `k` is the number of `s`'s crossings so far | none | `s`'s crossing `k`: from `g(i)`, `offered` |
| `spawnIn k` | the peer's crossing `k` is `offered` | `spawn` at the asker's global place | crossing `taken`; `s`'s next local place is the next global place |
| `sendIn k j` | the peer's crossing `k` is `offered`; `j` local | `comm asker g(j)` | crossing `taken` |
| `ack k i` | `s`'s crossing `k` is `taken` and its asker is `g(i)` | none | crossing `acked` |

The walk takes the head of `a` when it can be placed, otherwise the head of `b`, and refuses when neither can. At the end no crossing may be `taken`: one that was taken must be acknowledged. One still `offered` is allowed: its process is waiting, on its guest and in the replay.

Why the crossing's event sits at the taking guest's entry. The asker is held from `out` to `ack`, so no entry of its guest between those two reads or changes it, and its turn on `[]` depends on nothing else. Running that turn at the peer's `spawnIn` or `sendIn`, as the one-machine event does, and running it later at `ack`, as the guest did, lead to the same process. Two crossings in opposite directions can be acknowledged in an order that no single placement of fused events would satisfy; placing each event at its taking entry and treating `out` and `ack` as bookkeeping avoids that, and the greedy walk finds an order whenever one exists, because placing an entry never makes another unplaceable.

What the merge checks, and where each tamper is caught:

- An entry out of its log's order, dropped or repeated, with the chain as recorded: the link check (`acceptMark`), before the merge.
- For a chain made again by a guest that lies: a crossing taken twice, taken without being put out, acknowledged without being taken, a crossing number skipped or repeated, a place that does not exist: `combine` refuses. A taken crossing never acknowledged: `combine` refuses at the end.
- Entries that combine but are not what the program does (an event that cannot happen, a wrong process, a name made twice): the replay refuses.
- A record that replays but whose guest reported something else: the comparison of processes refuses.

## D-5. The check

`Surface.Cross.check` takes the program's bytes and the two records. It reads each record's chain, requires that each names the other and that the budgets agree, runs `combine`, begins the program with `beginRun budget`, runs the schedule with `schedRun budget`, and requires `.ran`. Then for each guest and each of its local places it compares the line the guest reported with the line of the process at the global place the merge gave. It answers `accepted`, the schedule and the processes, or `refused` and the first reason.

Lean owns all of it (D6): the entries, the guest's step, the packets, the merge, the replay and the comparison are Lean definitions. Zig opens connections, moves bytes, prints lines and checks signatures.

## D-6. Budgets

Every machine run a guest makes is one of `runPriced budget`, `settleRun budget`, `turnRun budget`, the functions `stepRun` uses, with the budget from the command line. The two halves of a crossing are the two runs of the one-machine event, each with the same budget, so the replay with that budget charges what the guests charged. The record carries the budget, and the checker refuses two records with different budgets.

A half that does not finish in its budget is not recorded. If the taking half does not finish, nothing was taken and the asker stays held. If the asker's turn at `ack` does not finish, the peer has already recorded the taking; the record is then refused, at the end of the merge or by the replay's `unfinished`. That run is not a run of the one-machine network within the budget, and the check says so.

## D-7. Proved, tested, assumed

Proved, in `kernel/Reflect/CrossingProof.lean`, stated in `kernel/CrossingContract.lean` with `#print axioms`, for every operation table, no `sorry`, no new axiom:

- `accepted_network`: when the replay of `combine a b` from `beginRun budget p` ends `.ran` at `cfg`, there is a configuration `c` with `Network sourceP p evs c` and `cfg` its compiled form. So `network_deterministic`, `Network.held_issued`, `Network.held_nodup` and `network_reflective` hold of an accepted record. This is `replay_true` applied to the merge: the checker accepts by replaying, and the theorem says an accepted record is a run.
- `combine_exact`: when `combine a b = some evs`, the entries the walk placed, in the order it placed them, are an interleaving of `a` and `b`: those of `a` in order are exactly `a`, and those of `b` exactly `b`. No entry is passed over, repeated or moved within its log.
- `combine_events`: the schedule is the events of those placed entries, in that order.

Tested, not proved:

- That the guests' own steps (`Surface.Cross`) produce logs that combine, and that the replay ends where the guests report. `kernel/CrossCheck.lean` runs two guests in one Lean process for several programs and both `take` settings; `unikernel/check-wire.sh` does it on two real guests.
- That each refusal is made by the check it is credited to: each tampered record is refused with its reason, and with that check undone in a copy of the tree the same test fails (`unikernel/evidence/`).
- Reading a record, the byte form of packets and the batching.

Not proved and not tested: that every pair of logs two honest guests can produce combines (the argument in D-4 is prose). No theorem speaks of a guest's step.

Assumed: Blake3 gives different entries different names (D5 of the vision); a valid signature (the host's check); that a name cannot be forged across machines; the image, the driver, QUIC.

## D-8. What is removed

`kernel/Surface/Remote.lean`, `kernel/RemoteCheck.lean`, `unikernel/remote-check.zig`, the exports `reflect_remote_offer`, `reflect_remote_take`, `reflect_remote_log`, `reflect_remote_same`, and the two requirements of `openspec/specs/channels/spec.md` that describe them. `examples/remote.hom` stays as a program; `examples/cross-*.hom` are the programs the check gives the guests.

## Open, not in this change

- Agreement between guests on an order (D10 of the vision says it is not provided).
- More than two guests. `Side` is two-valued and `Mix` holds two tables.
- A theorem about the guest's step: that two guests following `Surface.Cross` produce logs that `combine` accepts and whose replay equals their state.
- Keeping a guest's processes under a root between exchanges.
