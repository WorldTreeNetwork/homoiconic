# Design: a recorded crossing

## The shape

One program runs as processes spread over two guests, `a` and `b`. Guest `a` is given the program, as bytes over the wire, and starts it as its first process; guest `b` starts with none. The claim to check is that what the two guests did, taken together, is one run of `Reflect.Network` (`kernel/Reflect/Channel.lean`): one list of processes, one schedule.

Two events of the one-machine network involve two processes: a start (`Step.spawn`: the starter continues and the child begins) and a meeting (`Step.comm`: the sender continues and the receiver takes the message). Either can have its two processes on different guests. That is a *crossing*. Every other event is local to one guest.

## D-1. What each guest records

A guest's log is a list of entries, each one of five (`Reflect.Note`):

| Entry | Meaning | Machine run on this guest |
|---|---|---|
| `did ev` | The local event `ev` happened; places are this guest's own. | as `stepRun` |
| `out i k` | Process `i`'s request (a start or a send) was put out to the peer as this guest's crossing number `k`. `i` is held: no local event touches it until the acknowledgement. | `turnRun budget` of `i` on `[]`, run before anything leaves and kept aside |
| `spawnIn k` | The peer's crossing `k`, a start, was taken: the child began here as this guest's next process. | the child's start, `runPriced budget` then `settleRun budget` |
| `sendIn k j` | The peer's crossing `k`, a send, was taken: local process `j`, waiting to receive on that name and holding it, took the message. | `turnRun budget` of `j` on the message |
| `ack k i` | The peer took this guest's crossing `k`; process `i` continued on `[]`. | none: the turn kept at `out` is installed |

`k` counts a guest's own crossings from 0, so `out i k` is the `k`th `out` of its log. A crossing goes `out` on one guest, `spawnIn` or `sendIn` on the other, `ack` on the first. The request stays a rendezvous: the one who asked does not continue until the other side has taken it, as on one machine a send does not continue without a receive.

Written, an entry is `[mark, body]` with the existing link mark `[0, parent, order]` (`Reflect.readLink`), and its identifier is `Surface.Keep.entryName` of the pair, as for a VM's and a node's log. `Surface.Keep.acceptMark` reads the chain. No new record type: the body is new, the sealing and the link are the ones in place. The crossing reader is stricter than a VM's: a mark that is not `[0, parent, order]` with its order is refused, because `acceptMark` alone lets an unlinked mark through. Bodies: `[0, event]`, `[1, i, k]`, `[2, k]`, `[3, k, j]`, `[4, k, i]`.

A guest's record is its name, its peer's name, the budget, its log, the number of entries and the name of the last one (the head), and one line for each of its processes at the end (finished with what, or waiting on which payload, and the names held). The head is what stops a tail of the log being dropped with the chain as recorded: a chain says what comes before an entry, not what comes after. The head, the budget and the process lines are bound to the chain only by the signature over the whole record; a signature says which entity handed the record over, not that the record is true. The names are text to Lean, handed in by the image when the record is written. They are to be the entity key's public-name form (`add-entity-keys` design §1: Base58 of the 32-byte Blake3 fingerprint), `me.name` for the guest and `qconn.peer_name` for the other end. That change's code landed while this was being built, and the image now writes those names and signs the record's text with the entity key, printed as a `sig` line before the record; the signature over the record is checked by the host, as for a VM's log (`host/sig.zig`), by `unikernel/cross-check.zig`, which also requires the key that signed to be the entity the record names. The kernel never sees it.

## D-2. What crosses

Packets are data in the byte form (`Wire.write`), made and read by Lean:

- `[0, k, program, start, held]`: a start. `program` and `start` are the two data of the start request `[3, program, start]`, unchanged; `held` is `grant held start`, the names the starter holds that occur in the start data.
- `[1, k, name, message, held]`: a send on `name`. `held` is `grant held message`.
- `[2, k]`: the peer's crossing `k` was taken.

Any quoted program can cross, with any start data: nothing is compiled in. The child is a process of the receiving guest like any other; that guest's scheduler runs it to its end, or as far as the budget of each of its turns lets it.

The program. `add-entity-keys` takes the one file a guest is given at boot for the entity's key, so the program comes over the wire: a client sends the serving guest (`reflect.wire_port`) one `RFL1` run frame on the wire port, the program's byte form and the budget. That guest is side `a`. Zig checks the frame as the UDP service does; Lean reads the program (`Guest.give`). Until then side `a` waits and is not idle. A second program is not taken.

Transport: the guest with `reflect.peer` is the QUIC client and opens every exchange (the *caller*); the one with `reflect.wire_port` is the server, as now. One exchange is one connection: the caller's stream carries a batch, the server's answer carries a batch. The server takes batches from one entity only, the first that sent one. A batch is `[flag, got, budget, [[seq, packet], ...]]`. The guest with no program takes its budget from the first batch that carries one, so both run with the budget the program came with. Each guest numbers the packets it sends; `got` is how many of the peer's it has accepted, in order. A packet whose `seq` is not the next expected is dropped, and a guest sends again what the peer has not counted. So a lost or repeated exchange changes nothing. `flag` is 0 while the sender has work to do, 1 when it is idle, 2 when the caller has seen both idle with nothing in flight and closes. Batching, numbering and the flag are Lean's (`Surface.Cross`); Zig opens connections and moves the bytes.

Taking a batch only queues its packets. Every entry is recorded in `work`, which runs until no take, no local event and no put-out is possible, or until it has recorded 256 entries. So when two sends leave one guest in one batch, both are pending on the other before either is taken.

A guest is *idle* when `work` has nothing possible and it has no packet the peer has not counted. A pending send that no local receiver can take does not keep a guest from being idle. The caller closes (flag 2) when it is idle, the last answer said the server was idle, and that answer carried no packet. It repeats the closing exchange until it is answered. The server prints its record at the first flag 2 and answers every later one the same way. A guest has no other way to stop: a program that never goes idle, or a guest stopped between the peer's take and its own `ack`, gives no record or a pair that is refused. The soundness of an accepted record does not depend on any of this; only whether there is a record does.

## D-3. What a guest chooses, and the knobs

The local scheduler is `Reflect.pick` on the configuration with every held process masked as finished, so a held process is neither chosen nor found as the partner of a local receiver. The event `pick` gives for a new channel is not used as it stands: `pick` names it `nextName` of the local names, and the guest names it by parity instead (below). Three choices are the guest's and are not fixed by the semantics; each is recorded by the entry it produces:

- *Where a start goes.* `reflect.spawn=far` puts every start request of this guest out to the peer; without it a start is local.
- *When a send is put out.* When no local event is possible, a process waiting to send on a name it holds is put out to the peer, one at a time, lowest place first. Its turn on `[]` is run first; if that does not finish within the budget it is not put out, as one machine would report the meeting `unfinished`. Once out it is held, even if a local receiver appears later. A start that goes far is treated the same way.
- *Which pending send is taken first.* When several of the peer's sends could be taken by local receivers, `reflect.take=old` (default) takes the oldest, `reflect.take=new` the newest. This is the forced ordering the check uses: with two senders on `b` and one receiver on `a` that receives twice, the two settings record the two delivery orders.

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

The walk takes the head of `a` when it can be placed, otherwise the head of `b`, and refuses when neither can. An asker is held from its `out` to its `ack`: an entry that names a held place (a `did` event, another `out`, or the receiver of a `sendIn`) is refused. At the end no crossing may be `taken`: one that was taken must be acknowledged. One still `offered` is allowed: its process is waiting, on its guest and in the replay.

Why the crossing's event sits at the taking guest's entry. The asker is held from `out` to `ack`, so no entry of its guest between those two reads or changes it, and its turn on `[]` depends on nothing else. Running that turn at the peer's `spawnIn` or `sendIn`, as the one-machine event does, and running it later at `ack`, as the guest did, lead to the same process. Two crossings in opposite directions can be acknowledged in an order that no single placement of fused events would satisfy; placing each event at its taking entry and treating `out` and `ack` as bookkeeping avoids that, and the greedy walk finds an order whenever one exists, because placing an entry never makes another unplaceable.

What the merge checks, and where each tamper is caught:

- An entry out of its log's order, dropped from the middle or repeated, with the chain as recorded: the link check, before the merge. Entries dropped from the end: the head.
- For a chain made again by a guest that lies: a crossing taken twice, taken without being put out, acknowledged without being taken, a crossing number skipped or repeated, a place that does not exist: `combine` refuses. A taken crossing never acknowledged: `combine` refuses at the end.
- Entries that combine but are not what the program does (an event that cannot happen, a wrong process, a name made twice): the replay refuses.
- A record that replays but whose guest reported something else: the comparison of processes refuses.

Not refused: the comparison is of lines, a finished value or a payload and the names held. It does not compare what a waiting process will do next. A guest that lies, makes its chain again, and drops or repeats one turn of a loop that sends the same message on the same name can hand over a record that is accepted. That record is still a run of the one-machine network, and its lines are that run's; it is not the run the guest made. Also not refused: the order of a guest's `ack` entries is not compared with the order in which the peer took the crossings. The taking guest's log holds the delivery order; the asking guest's record of a run with the takings in the other order combines with it (`kernel/CrossCheck.lean`).

## D-5. The check

`Surface.Cross.check` takes the program's bytes and the two records. It reads each record's chain, requires that each names the other and that the budgets agree, runs `combine`, begins the program with `beginRun budget`, runs the schedule with `schedRun budget`, and requires `.ran`. Then for each guest and each of its local places it compares the line the guest reported with the line of the process at the global place the merge gave. It answers `accepted`, the schedule and the processes, or `refused` and the first reason.

Lean owns all of it (D6): the entries, the guest's step, the packets, the merge, the replay and the comparison are Lean definitions. Zig opens connections, moves bytes, prints lines and checks signatures.

## D-6. Budgets

Every machine run a guest makes is one of `runPriced budget`, `settleRun budget`, `turnRun budget`, the functions `stepRun` uses, with the budget from the command line. The two halves of a crossing are the two runs of the one-machine event, each with the same budget, so the replay with that budget charges what the guests charged. The record carries the budget, and the checker refuses two records with different budgets.

A half that does not finish in its budget is not recorded. If the taking half does not finish, nothing was taken and the asker stays held. The asker's turn is run before its request leaves, so an `ack` cannot fail for budget: a request whose asker would not finish is never put out.

## D-7. Proved, tested, assumed

Proved, in `kernel/Reflect/CrossingProof.lean`, stated in `kernel/CrossingContract.lean` with `#print axioms`, for every operation table, no `sorry`, no new axiom:

- `accepted_network`: when the replay of `combine a b` from `beginRun budget p` ends `.ran` at `cfg`, there is a configuration `c` with `Network sourceP p evs c` and `cfg` its compiled form. So `network_deterministic`, `Network.held_issued`, `Network.held_nodup` and `network_reflective` hold of an accepted record. This is `replay_true` applied to the merge: the checker accepts by replaying, and the theorem says an accepted record is a run.
- `combine_merged`: `combine a b = some evs → Merged a b evs`. `Merged` is the table of D-4 as a relation, defined apart from the walk: from the first state, each step places the head of one log by `Mix.place`, in any order, the events are those `place` gives in that order, and the last state has no crossing `taken`. So the function does only what the table allows.
- `merged_exact`: in any `Merged` walk the entries placed, in order, keep `a` whole and in order and `b` whole and in order. This is true of any walk that consumes both lists and says little by itself; it is stated so that "no entry passed over or moved" is a theorem and not a reading of the code.
- `merged_once`: in any `Merged` walk no crossing is taken twice: the `spawnIn` and `sendIn` entries of one guest name different crossings. (If this proof does not land it is listed under tested.)

The converse, that the greedy walk finds a schedule whenever some `Merged` walk exists, is argued in D-4 and not proved.

Tested, not proved:

- That the guests' own steps (`Surface.Cross`) produce logs that combine, and that the replay ends where the guests report. `kernel/CrossCheck.lean` runs two guests in one Lean process for several programs and both `take` settings; `unikernel/check-wire.sh` does it on two real guests.
- That each refusal is made by the check it is credited to: each tampered record is refused with its reason, and with that check undone in a copy of the tree the same test fails (`unikernel/evidence/`).
- Reading a record, the head, the byte form of packets, the batching and the closing exchange.

Not proved and not tested: that every pair of logs two honest guests can produce combines (the argument in D-4 is prose). No theorem speaks of a guest's step.

Assumed: Blake3 gives different entries different names (D5 of the vision); a valid signature (the host's check); that a name cannot be forged across machines; the image, the driver, QUIC.

## D-8. What is removed

`kernel/Surface/Remote.lean`, `kernel/RemoteCheck.lean`, `unikernel/remote-check.zig`, the exports `reflect_remote_offer`, `reflect_remote_take`, `reflect_remote_log`, `reflect_remote_same`, and the two requirements of `openspec/specs/channels/spec.md` that describe them; its third, the hypothesis about names, moves to the new `crossing` spec. The prose that names them goes too: the opening and Purpose of the channels spec, the opening of `openspec/specs/zig-host/spec.md`, and "the remote exchange" in `openspec/specs/bytecode-machine/spec.md`. `unikernel/build-net.sh` stops building `remote-check`, and `unikernel/check-wire.sh` stops running `RemoteCheck.lean`. `examples/remote.hom` stays as a program; `examples/cross-*.hom` are the programs the check gives the guests.

## Open, not in this change

- Agreement between guests on an order (D10 of the vision says it is not provided).
- More than two guests. `Side` is two-valued and `Mix` holds two tables.
- A theorem about the guest's step: that two guests following `Surface.Cross` produce logs that `combine` accepts and whose replay equals their state.
- Keeping a guest's processes under a root between exchanges.
