# Design: harden the crossing

The crossing as it stands is `openspec/specs/crossing/spec.md` and the design of `openspec/changes/archive/2026-11-24-add-recorded-crossing/` (D-1 to D-7 there; "the old design" below). This change keeps its shape: two guests, one log each, `combine`, one replay. It changes what a guest runs with, what it may hold, and what the check compares. The advise read sent the first draft back; its findings are answered at the end and in place.

## D-1. A guest's budgets are its own (`q59.79`)

**Now.** Side `a` runs with the step budget of the program's frame. Side `b` starts with budget 0 and takes the first nonzero budget a batch carries (`Guest.take`), so the peer chooses `b`'s budget, without bound. Every turn of either guest may make `Reflect.turnSpace` = 4000000 cells, the kernel's constant, which no record states.

**Two budgets, each the guest's own.** A guest has a *step limit* and a *turn limit* (cells a turn may make), its own: the words `reflect.budget=<steps>` and `reflect.turn=<cells>`, or `Cross.defaultLimit` = 100000000 steps and `Cross.defaultTurn` = 500000 cells. It runs every machine run with a step budget and a turn space, each the least of:

- its own limit;
- for the steps on side `a`, the budget of the frame that gave it the program;
- every value the peer's batches announced before this guest *fixed* its budgets.

A guest fixes both when it first runs anything: side `a` when it begins the program, side `b` when it first works a packet. After that a batch's numbers change nothing. A batch announces the guest's two numbers as they stand: `[flag, got, steps, cells, [[seq, packet], ...]]` (a batch had one number; its byte form changes).

**Why the two agree.** Side `a` does not begin the program until it has taken one batch from the peer (`heard`); until it begins it is not idle (as now). So `a`'s fixed numbers are at most what that batch announced, which is at most `b`'s limits. `b` works no packet until one of `a`'s arrives; every packet of `a`'s leaves after `a` began, in a batch that announces `a`'s fixed numbers; `b` takes the least of those and its own before it works the packet, which gives `a`'s. (Whatever `b` lowered to earlier is at least `a`'s, since `a`'s are the least of everything either announced.) In `net.zig`, `b` is the caller and opens every exchange, so `a` hears `b` in the first exchange, whether the program arrives before or after it; `a` begins in `crossSettle` or in its own `work` once both have happened. If `a` were the caller the same holds with one more exchange. The advise read traced both orders against `net.zig` and found no honest pair that disagrees.

A peer that lies can lower this guest's numbers, never raise them; if it announces one budget and runs with another, the records differ and the check refuses them.

**The replay takes the turn space as a parameter.** One step budget and one turn space for both guests is what lets one replay stand for both. The channel runs get a cells argument: `runTurnIn cells budget s` in `Space.lean` (what `runTurn` was, with `cells` for `turnSpace`; `runTurn budget = runTurnIn turnSpace budget`), and `settleIn`, `turnIn`, `stepIn`, `schedIn`, `beginIn` in `Channel.lean`, with `settleRun`, `turnRun`, `stepRun`, `schedRun`, `beginRun` their instances at `turnSpace`. Every other driver (requests, the log, the node, the keep session, `autoRun`) keeps `turnSpace` and does not change. The soundness theorems of `ChannelProof.lean` are proved for every `cells` and the old ones follow. `Reflect.accept` takes the cells too, and `accepted_network` is stated for every cells and budget.

**What the record says.** `budget <steps> <cells>`, what every turn ran with, and `own <steps> <cells> <hold>`, the guest's own limits (the hold is D-2). The check requires the two records' `budget` lines equal, each at most its record's `own`, and each within the checker's own ceilings (D-3, "What the check bounds").

## D-2. A guest bounds what it holds (`q59.71`)

### What a guest holds

Between turns a guest keeps: each process's status and the names it holds (`cfg`); for each crossing it put out and that is not acknowledged, the turn it ran and kept (`asked`); the packets it sent that the peer has not counted (`sent`); the peer's packets accepted and not worked (`inbox`) and the peer's sends waiting for a receiver (`pending`); and its log. Each turn's runs are bounded (`runTurnIn`), but nothing bounds the sum, so a program that keeps a little each turn, or starts processes that each keep a turn's worth, ends the guest.

### The measure: a ledger, and a count when it is spent

`add-space-budget` showed that no function of a machine state measures what it holds, and settled on a ledger of cells *made*, pure and proved, with the runtime's count of cells *held* (`reflect_live_cells`) asked when the ledger is spent. The same is done here one level up: the ledger is the guest's, charged entry by entry, and the count is of the whole guest object.

The guest has a *hold* `H`, its own: `reflect.hold=<cells>`, or `Cross.defaultHold` = 2000000. It is not negotiated: each side's ledger is its own, and the record states it. It keeps a credit, `H` at the start. Each entry it records is charged (below). Then:

- the charge `c` is at most the credit: the credit falls by `c`;
- otherwise the guest counts the cells it holds, `m`, and records the count at once as an entry: `held m` when `m ≤ bar H` (`H - H / 4`, as `Space.bar`), and the credit becomes `H - m`; otherwise `full m`, and the guest is *full*.

The entries are `[5, m]` and `[6, m]`; they emit no event and `combine` places them anywhere. Counting after the entry lets the count see what the entry made. A count is not charged, and after `full` nothing is charged.

**The record's own bound.** Counts give back the cells of the log, but a log is printed in full at the end, at about 120 bytes an entry against three objects held. So the record is bounded apart from the ledger, by two pure caps the replay checks exactly: a side records at most `entryLimit` = 60000 entries before `full`, and has at most `procLimit` = 4096 processes. An entry that brings the log to `entryLimit` or the processes to `procLimit` is followed at once by `full m` (with the count taken as always), whatever `m` is. After `full` come at most the acknowledgements still owed, at most `outLimit` = 64. A process line is at most about 400 bytes (D-3). So a record is at most about 7.3 MB of entries and 1.6 MB of lines, inside the 16 MiB record buffer.

**A full guest** does nothing more but what it owes: it takes no packet but acknowledgements (`[2, k]`) and records their `ack`s, so that every crossing the peer took is acknowledged and the two logs still combine; a start or a send of the peer's that arrives is dropped, and that crossing stays `offered`, which the merge allows. It does no local event and puts nothing out. It goes idle and closes as any guest does. The check says so (`full a: entry <n>, <m> cells counted`). That is the outcome of a program that holds too much: a record, not a panic.

### The charge of an entry

| entry | charged (cells) |
|---|---|
| any but a count, before `full` | `entryCells` = 32 |
| `did (fresh i n)` | the cells `i`'s turn made |
| `did (comm i j)` | the cells both turns made |
| `did (spawn i)` | the starter's turn on `[]`, the child's start and settle, `procCells` = 128, and `codeCells prog` = 2 × the cells of the quoted program |
| `did (answer i x)` | none: a guest never records one, and the check refuses it (`an answer from outside in a crossing`) |
| `out i k` | `i`'s turn on `[]` (kept in `asked`), and the cells of the packet put out |
| `spawnIn k` | the child's start and settle, `procCells`, `codeCells prog`, the cells of the packet taken and of the `[2, k]` sent |
| `sendIn k j` | `j`'s turn on the message, the cells of the packet taken and of the `[2, k]` sent |
| `ack k i` | nothing more (the turn was charged at `out`) |
| `held m`, `full m`, anything after `full` | nothing |

A *turn* is two runs, the resume and the settle (`turnIn`), so a turn may make `2 × cells`. Side `a` begins the program before it records anything; that is charged to its credit first: the start and settle, `procCells` and `codeCells` of the program. If it passes the credit the first entry is a count.

"The cells a run made" is the ledger of `runSpace`: the turn space less the credit left when the run ended. `runSpace` gives no credit back, so `Reflect/Hold.lean` adds `runSpaceLeft` (the same recursion, giving the credit too) and *measured* variants of the channel runs: `runTurnMade`, `settleMade`, `turnMade`, `beginMade`, and `stepMade cells budget cfg ev`, which gives the cells made by process `i`'s side of the event and by the other's apart. Each gives, as its first part, exactly what `runTurnIn`, `settleIn`, `turnIn`, `beginIn` and `stepIn` give (proved). The cells of a data value are `cellsOf`, as `Data.cells` counts them, as a walk with a list of work. `codeCells` takes the term and the code made from a quoted program as at most twice the cells of its data form, by reading `unreify` and `compile` (`Machine.lean`: one term node for each array of the form, which has at least five cells, and at most a few instructions for each term node); this is part of the charge table that is read, not proved, as in `add-space-budget`.

### The replay is the ledger's replay

The check replays the schedule once, in the order the walk placed the entries (`combineTrace` gives that order; `combine` is its projection), with the measured runs, keeping each side's charges (`traceRun`). A crossing is charged as the guests charged it: at `out`, the asker's turn on `[]` from its status in the replay at that point (it is held from `out` to `ack`, so the event at the taking runs that same turn); at the taking, the event's other half; a local event, both halves. Side `a`'s begin is charged from `beginMade`. Proved: when `traceRun` runs every event, its configuration is what `schedIn` gives for the same schedule (`traceRun_sched`), so `accepted_network` speaks of what the check ran.

It then walks each side's entries, in its log's order, with their charges (`Hold.walk`):

1. an entry whose charge passes the credit must be followed at once by a count (`the ledger was spent and not counted`);
2. a count must follow such an entry or a cap (`a count where the ledger was not spent`);
3. `held m` with `m` past the bar is refused (`a count past the bar that is not full`), and `full m` with `m` within it and no cap reached (`full within the bar`);
4. an entry that reaches `entryLimit` or `procLimit` must be followed by `full` (`a cap reached and not full`);
5. after `full m`, only `ack` entries, at most `outLimit` (`an entry after full`).

So the replay reaches the same outcome as the guest wherever the ledger or a cap decides it, and the count decides only what the guest says it counted. The check cannot verify `m`: the count is a property of the guest's objects, not of the state. A guest that lies about `m` can say it was full when it was not, which only stops its own run, or go on when it was full, which only risks its own memory.

### What the peer can make a guest hold

The ledger charges what the guest's program does. What the peer sends arrives before it is an entry, so plain limits cover it:

- a guest puts out at most `outLimit` = 64 crossings not acknowledged: a process that would put out a 65th is hidden from the scheduler as a held one is, and the guest goes on with everything else;
- it produces no packet (puts nothing out and takes nothing) while `2 × outLimit` of its packets are not counted by the peer; an honest peer counts at its next exchange;
- it accepts at most `queueLimit` = `2 × outLimit` packets into `inbox` and `pending` together; a packet past that is not accepted (`got` does not count it) and the peer sends it again later. An honest peer never has more than 64 crossings out and 64 acknowledgements owed, so it never meets the limit;
- a packet is at most the 8 KiB a batch's stream carries;
- `sent` is a list (the runtime's count does not look inside an array, `ffi.c`), and packets the peer has counted are dropped from it.

The limit of 64 crossings out can leave a program stuck that another schedule would finish; the old design already admits that a guest's choices can do that.

### Memory

At any time a guest holds at most `H` cells by the ledger's account plus one entry. The worst entry is a local start or a local meeting: four runs of at most the turn space each (two turns), and for a start the code of the quoted program its payload holds, which a payload's bound (`4 × cells` written) puts at no more than `4 × cells` cells. At the defaults that is `2000000 + 8 × 500000` = 6 million cells, 144 MiB at 24 bytes a cell. On top: the walk's table and stack for a cut of 1.5 million (16 and 12 MiB); the queue between counts, at most 128 packets of 8 KiB, about 1 MiB of bytes and under 1 million cells once read; and at the close the record, at most 16 MiB as text, its bytes and the static buffer. That is about 230 MiB against the 360 MiB of the image's `mmap` area. The worst program (D-7, `cross-worst.hom`) is run on the image to check it, and the peaks are recorded in `unikernel/README.md`. `cross-deep.hom` builds more than a turn of the default may (24 turns, each building 40000 levels of data and 6000 of program) and holds more than the default hold by design: its run is given `reflect.turn=4000000 reflect.hold=16000000`, which is the guest owner's choice to give it more memory.

## D-3. What the check compares (`q59.69`)

### A root on each process line

A process line is `<status>; holds <names>; <digest>`:

- `<status>` is the payload or the result, printed when it is at most 512 written (`Data.writes`), and otherwise `waiting on more than 512 written` or `more than 512 written`;
- `<names>` is the list of names held when there are at most 32, and otherwise `<n> names`;
- `<digest>` is `root <hex>`, the Blake3 hash of the byte form (`Wire.write`) of `[names held, status]`, with the status in the data form of machine values (`Wire.valueData`): `[0, function, payload]`, `[1, value]`, `[2, i]` or `[3]`; or, when that form does not fit, `data <hex>`, the same hash with the function left out (`[0, payload]`, and `[1]` for a finished function); or `root none` when neither fits.

The form of a function is a tree: each value it captured is written where it is held, so it can be far larger than what is held (`Wire.fitsValue`). So a digest is made within a room: a side has `sideRoom` = 64000000 units of `Wire.valuesFit`, used in local order; a process may use at most `procRoom` = 4000000 of it for its root; when its root does not fit in that, its `data` digest is tried with what is left of the side's room. A process uses what it used, or `procRoom` if its root did not fit, whichever is less than what is left. Data is bounded (a payload or a result is at most `4 × cells` written, `runTurnIn`), so at the defaults a process has a `data` digest whenever the side's room is not used up, which takes more than 30 processes holding the largest payloads there are. The guest and the replay run the same rule on the same states and agree on which processes have which digest; a guest cannot choose a weaker digest for a process than the replay gives it.

The replay computes the line of its process the same way and the check compares lines as it does, so the digest is compared wherever a line is.

**Why not `Wire.save`'s root.** `same_root` is about `save` of a piece. `save` cuts with `cut`, which recurses on the native stack once for each level of a list and of nesting, as does `pieceItem`; a process that finished with a list of 100000 items, or `cross-deep`'s data, would end the guest in a full stack (`homoiconic-q59.72`). `Wire.valueData` and `Wire.write` are walks. The digest has the property that matters: equal states give one digest, since it is a function of the state, and one digest names one state, since the byte form reads back to its value (P4, tested) and Blake3 names one byte string (D5). Nothing fetches pieces under it. A Merkle hash memoised by address (the advise read's suggestion) would remove `root none`, at the price of trusted C whose answer must be shown to be a function of the value; it is left as an option.

### Acknowledgements in the order of the takings

A guest records `ack k` when the peer's `[2, k]` arrives; the peer sends `[2, k]` at the entry where it took crossing `k`, packets are numbered and taken in order, `inbox` is worked in order, and a full guest still records acknowledgements. So in two honest records, the crossings guest `s` acknowledges, in its log's order, are exactly the crossings of `s` the other guest took, in the other's log's order (every crossing taken is acknowledged before the two close, the old design's D-2). The check requires it, in both directions (`the acknowledgements of b are not the order a took them in`), after the merge and before the replay.

It closes a real gap: until now `a`'s record of one run and `b`'s record of a run with the takings the other way combined and were accepted (`kernel/CrossCheck.lean`, "the acknowledgements in another order still combine"). It also pins, for each guest, the order of its takings of the peer's crossings to the peer's signed record: the test "the takings in another order" is now refused here, before the comparison of lines would refuse it.

### What the check bounds

The check is given the records and nothing else, so it bounds its own work: a record of at most 16 MiB (`cross-check`), a step budget at most `Cross.defaultLimit`, a turn space at most `Reflect.turnSpace`, a hold at most 64000000 (`the record asks more than this check runs`). A record whose stated own limits are above these is refused, which is the check's choice of what it will replay, not a fault of the record.

### What a lying guest can and cannot do afterwards

Each guest signs only its own record, and nothing attests what a guest ran. So the claim is about one guest that lies, checked against the signed record of one that does not.

A record of guest `s` that the check accepts beside an honest peer's is, on `s`'s side:

- a log that, with the peer's log, combines and replays as a run of the one-machine network (`accepted_network`);
- crossings, takings and acknowledgements that agree with the peer's at every crossing: the same crossing numbers out and taken (`combine`), and the peer's takings of `s`'s crossings acknowledged in the order the peer took them;
- a final state of each of `s`'s processes whose line and digest are exactly what that replay ends with;
- counts and `full` placed where that replay's ledger and caps put them;
- the same step budget and turn space as the peer's record, at most `s`'s stated limits and the check's ceilings.

So `s` cannot:

- hand over a log with a final state that is not that log's: the q59.69 lie, a log with a turn dropped or repeated reported with the state the guest actually reached, is refused wherever the process has a `root` or `data` digest that covers what changed (a `data` digest does not cover a function; `root none` covers nothing but the line);
- take a crossing twice, take one that was not put out, leave one taken unacknowledged, drop one it took (`combine`);
- acknowledge the peer's takings in another order than the peer took them, or pair its record with a record of another delivery order of the peer's;
- hand over a record with another step budget or turn space than the peer's;
- say it was full, or counted, where its ledger and caps do not put it, or record more than acknowledgements after `full`.

And `s` can still:

- hand over a record of a *different run* of the same program, made whole: its own local events, their interleaving with the crossings, which of its processes it says asked, and when it put a request out, all other than what it did, provided the result is a run that agrees with the peer at every crossing and its lines and digests are that run's. It can compute those itself: its processes depend only on its own entries and the packets it was sent. The check cannot tell this from the run it made; a signature says who handed a record over, not that it is true. Run on its own, the check cannot tell which of two records lies.
- make the honest peer's record refused, with a reason that may name the honest side: put out a packet whose message or names are not what its own log replays to, send `[2, k]` for a crossing never taken, or withhold an acknowledgement. The check refuses the pair and cannot tell who lied.
- change the honest peer's run, within what the program allows: announce a budget of 1 step or a turn space of 1 cell before the peer fixes its own, so that every turn of the run is unfinished; fill the peer's queue with 128 packets of 8 KiB; start children on the peer that each hold what a turn allows, until the peer is full. Each is a run the check accepts and reports as such.
- choose the counts it reports, within where the ledger puts them: call itself full early, or say `held` with a small count. That changes whether its run went on, not what the run is.
- state its own limits and hold as it likes, within the check's ceilings, as long as what it ran with is at most what it states.
- stop: give no record, or a record that the peer's does not combine with (liveness).

Two guests that lie together can hand over any run of the program: the check has nothing honest to hold them to.

## D-4. The record's form

A record is text, one item per line, signed whole by its guest (`add-entity-keys`):

```
form 2
me <entity name>
peer <entity name>
budget <steps> <cells>                 -- what every turn ran with
own <steps> <cells> <hold>             -- this guest's own limits
entry [[0, parent, order], body]       -- bodies [0, event] [1, i, k] [2, k] [3, k, j] [4, k, i] [5, m] [6, m]
...
head <entries> <name of the last>
proc <status>; holds <names>; root <hex> | data <hex> | root none
...
```

`form 2` marks the form: the old form had no such line and is refused (`record a: not of form 2`). Every header line is required. `cross-check.zig` finds the `me` line after `form` when it checks that the key that signed is the entity named. The batch's byte form changes as D-1 says; packets do not.

## D-5. The exports and the image

- `reflect_cross_start(flags, limit, turn, hold)`: the guest's own limits; 0 means the default.
- `reflect_cross_give(g, program, length, budget)`: as now; the budget is a ceiling.
- `reflect_cross_work(g)`: works with the runtime's count of the guest (`reflect_live_cells` on the Lean guest object, cut at the bar of its hold). `kernel/CrossCheck.lean` runs under Lean's evaluator, which cannot call it; there a guest's count is a parameter: the ledger alone (a count that always answers "too many", as `Space.ledger`), or a fixed number to make `held` entries.
- `unikernel/net.zig`: the words `reflect.budget=<steps>` (1 to 2^64 − 1), `reflect.turn=<cells>` (1 to 2^64 − 1) and `reflect.hold=<cells>` (a whole number below 2^64), each at most once, only on an end of the crossing; the record buffer grows from 256 KiB to 16 MiB.
- `unikernel/cross-check.zig`: its record buffers and its output grow to 16 MiB and 64 MiB; it finds `me` after `form`.

## D-6. Proved, tested, assumed

Proved, stated in `kernel/CrossingContract.lean` with `#print axioms`, no `sorry`, no new axiom:

- `accepted_network` for every turn space and budget (it was stated at `turnSpace`; the statement gains `cells`), `combine_merged`, `merged_exact`, `merged_once`, `Walk.once`, with the two new entries in `Note`.
- `combineTrace_walk`: the order the check replays in is a `Walk` of the two logs, so each side's entries are charged in its log's order (`Walk.exact`).
- `traceRun_sched`: when the check's replay runs every event, its configuration and events are `schedIn`'s on the schedule `combine` gives.
- `runSpaceLeft_fst`, `runTurnMade_fst`, `settleMade_fst`, `turnMade_fst`, `beginMade_fst`, `stepMade_fst`: the measured runs are the runs.
- The channel soundness theorems (`settleRun_sound` to `replay_true`) for every turn space; the old statements follow.
- Of `Hold.walk`, when it accepts a side: every stretch from the start or a count up to the next count charged, without its last entry, at most the credit it began with (`hold_stretch`); a `held m` is at most the bar and the next stretch begins with `H - m` (`hold_count`); after a `full` come only acknowledgements, at most `outLimit` (`hold_full`); the side has at most `entryLimit + outLimit + 1` entries (`hold_entries`).

Tested, not proved: the guest's step (budgets, the ledger, the caps and limits, the lines); that the replay's charges are the guest's; reading a record; the image.

Assumed: Blake3 names one byte string and the byte form one value (D5, D7); the runtime's count (`add-space-budget`); that the charge table covers what Lean allocates; the signature; that a name cannot be forged across machines.

## D-7. The checks and their controls

`kernel/CrossCheck.lean` (two guests in one process) and `unikernel/check-wire.sh` (two real guests). Each new refusal is asserted with its reason, and `kernel/cross-controls.py` undoes its check in a copy of the kernel and requires the test to fail. A test credited to a rule is one that only that rule catches.

| test | where | refused with / ends in | control |
|---|---|---|---|
| the peer announces a huge budget and turn in a batch | Lean | `b` runs with its own limits; its record's `budget` line is its own | `take` takes the peer's numbers |
| the program comes with more steps than the peer allows | Lean, wire | both records `budget <the lower>`, accepted | side `a` takes no number from the peer |
| a budget above its own limit | Lean, wire | `record b: its budget is above its own limits` | the comparison removed |
| a record that asks more than the check runs | Lean | `the record asks more than this check runs` | the ceiling removed |
| another turn space in one record | Lean | `the budgets differ` | — (the existing comparison) |
| a record of the old form | Lean | `record a: not of form 2` | the form not read |
| `examples/cross-grow.hom`: one process keeps more each turn for 3000 turns, then waits | Lean, wire | accepted, `full a`; on the image no panic | the guest's ledger removed (Lean: it finishes, not full) |
| `examples/cross-grow-forever.hom` with `reflect.hold=18446744073709551615` | wire | `INTERNAL PANIC: out of memory` | (it is the control of the hold on the image) |
| `examples/cross-fan.hom`, `spawn=far`: children on `b` that each keep a turn's worth | Lean, wire | accepted, `full b` | as above |
| `examples/cross-worst.hom`: held near the bar, then a local meeting whose four runs each build the most a run may | wire | accepted, `full a`, no panic; its peak recorded | — |
| a loop of 70000 local events | Lean | accepted, `full a` at entry 60000 (the cap) | the cap removed |
| counts recorded (a fixed count in Lean) | Lean | accepted, `hold a: … counts` | — |
| a count dropped; a count inserted where nothing was spent; `held` past the bar; `full` within the bar; an entry after `full`; re-signed | Lean | each its `hold a: entry n: …` reason | each rule of `Hold.walk` removed |
| a batch of 200 packets | Lean | `got` counts 128 | the queue limit removed |
| 70 sends put out to a peer that never takes them | Lean | 64 crossings out | the out limit removed |
| a peer that never counts | Lean | `sent` stops at 128 | the sent limit removed |
| a process whose payload writes more than 512 | Lean | its line says `more than 512 written` and the check still accepts | — |
| a process whose function form does not fit `procRoom` | Lean | `data <hex>` on its line | — |
| a different run, re-signed, with the state it had (`examples/cross-hidden.hom`: a local race whose two deliveries are swapped; its lines are the same, its receiver's closure is not) | Lean, wire | `process 0 (a 0): reported …; root X, replayed …; root Y` | the digest left off the line |
| one guest's record of one delivery order with the other's of the other | Lean, wire | `the acknowledgements of b are not the order a took them in` | the order not compared |
| the takings in another order, chain made again | Lean, wire | `the acknowledgements of b are not the order a took them in` | the order not compared |
| a different run made whole: the swapped log with the replay's lines | Lean | accepted (what a lying guest can still do) | — |
| an answer from outside in a log | Lean | `an answer from outside in a crossing` | — |

## D-8. Open, not in this change

- More than two guests (`Side` is two-valued, `Mix` holds two tables): a new bead.
- That every pair of honest logs combines, and a theorem about a guest's step (`homoiconic-q59.68`).
- A count that is a function of the state (`homoiconic-q59.74`), which would let the check verify the counts.
- A run nonce in both records, so that records of two runs cannot be paired even when they agree at every crossing. Two such records describe the same exchanges; nothing a nonce adds is checked here.

## The advise read, answered

`reviews/2026-11-25-advise.md` (Opus, fresh context, before code): send-back, three blockers and thirteen more. The budget agreement and the acknowledgement order were found sound, and the root choice justified. In its order:

1. *A full guest's record does not fit 16 MiB*: counts give back the log's cells, and shared values print many times. Two pure caps the replay checks, `entryLimit` and `procLimit`, end in `full`; lines are bounded (512 written of status, 32 names, one digest); the arithmetic is in D-2.
2. *The worst entry is four runs, not two*: a turn is a resume and a settle. The crossing's turn space is now the guest's own and negotiated, default 500000, carried through the channel runs as a parameter, and the memory sum is per entry; `cross-worst.hom` runs the worst entry on the image.
3. *The count does not see `sent`*: `sent` is a list, trimmed of what the peer counted, and a guest produces no packet while 128 are uncounted.
4. *`cross-check.zig` requires `me` first*: it finds `me` after `form`; its output grows.
5. *"The takings in another order" moves*: it is now an acknowledgement-order test, and its control and the `unikernel-net` delta say so; the comparison is credited with `cross-hidden`.
6. *Large values become less checked*: a `data` digest is on the line whenever the root does not fit; a process uses at most `procRoom`; one wording, `more than 512 written`.
7. *Charging after `full`*: nothing is charged after `full`.
8. *The list of what a lying guest can do*: it now says the liar can get an honest record refused, lower the peer's budget to one step, fill the peer, and that the check cannot tell who lied; the check has its own ceilings; "cannot run with" is "cannot hand over a record with".
9. *Tests and controls*: tests for the out, queue and sent limits, the caps, long lines and `data` digests; one test per rule of `Hold.walk`; `cross-grow.hom` stops on its own and `cross-grow-forever.hom` is the image control; `cross-hidden.hom` makes no count.
10. *The check's replay and `accepted_network`*: the check replays once, by `traceRun`, and `traceRun_sched` ties it to `schedIn`.
11. *`did (answer i x)`*: refused by the check.
12. *At the out limit*: the process is hidden and the guest goes on.
13. *`queueLimit`*: defined as `2 × outLimit`.
14. *The memory sum*: the queue, the record at the close and its buffer are in it.
15. *A Merkle hash by address, a run nonce*: both left as options (D-3, D-8), with the reason.
16. *Fixing side `b`*: it fixes when it first works a packet.
