# Design: harden the crossing

The crossing as it stands is `openspec/specs/crossing/spec.md` and the design of `openspec/changes/archive/2026-11-24-add-recorded-crossing/` (D-1 to D-7 there; "the old design" below). This change keeps its shape: two guests, one log each, `combine`, one replay. It changes what a guest runs with, what it may hold, and what the check compares.

## D-1. A guest's budget is its own (`q59.79`)

**Now.** Side `a` runs with the budget of the program's frame. Side `b` starts with budget 0 and takes the first nonzero budget a batch carries (`Guest.take`). So the peer chooses `b`'s budget, without bound.

**The rule.** Each guest has a *limit*, its own: the word `reflect.budget=<steps>` on its command line, or `Cross.defaultLimit = 100000000` (the most a frame may ask, `budget_max` in `net.zig`). The budget it runs every machine run with is the least of:

- its limit;
- for side `a`, the budget of the frame that gave it the program;
- every budget the peer's batches announced before this guest *fixed* its budget.

A guest fixes its budget when it first runs anything: side `a` when it begins the program, side `b` when it records its first entry. After that a batch's budget changes nothing. A batch announces the guest's budget as it stands.

**Why the two agree.** Side `a` does not begin the program until it has taken one batch from the peer (`heard`), so `a`'s fixed budget is at most the budget that batch announced, which is at most `b`'s limit. `b` records nothing until a packet of `a`'s arrives; every packet of `a`'s leaves after `a` began, in a batch that announces `a`'s fixed budget; `b` takes the least of that and its own, which is `a`'s, before it works the packet. (Whatever `b` lowered to before `a` began is at least `a`'s fixed budget, since `a`'s is the least of everything either announced.) In order:

1. `b` (the caller in `net.zig`; in `simulate` too) opens an exchange announcing `L_b`. Its budget is `L_b`; nothing is fixed.
2. `a` takes it: `heard`, budget `min(L_a, frame, L_b)`. It begins the program now (or as soon as it is given it) and fixes that budget, `B`.
3. Every later batch from `a` announces `B ≤ L_b`; `b` lowers to `B` on the first, before it takes any packet in it (taking a batch only queues; the budget is read first), and fixes `B` with its first entry.

If `a` is the caller instead, step 1 is `a` announcing `min(L_a, frame)` without beginning, and the rest is the same with one more exchange. A peer that lies about its budget can lower this guest's, never raise it; if it announces one budget and runs with another, the two records' budgets differ and the check refuses them (`the budgets differ`), as now.

A guest that runs nothing before it is fixed is what makes this hold, so it is a rule of the guest (`Guest.step` does nothing on side `a` until `heard`). Waiting to hear costs side `a` one exchange at the start.

**What the record says.** `budget <B>`, the budget every turn ran with, and `limit <L>`, the guest's own. The check requires the two budgets equal (as now) and each at most its own limit (`record a: its budget is above its own limit`). The replay runs every turn with `B`, as now: one budget is what makes `schedRun budget` the replay of both guests, and `accepted_network` is unchanged. Per-side budgets in the replay were the alternative: a crossing's two halves run on two guests, so a comm would need a step run with two budgets, and a new replay and its proof; agreeing on one budget costs one exchange and changes no theorem.

**The cells a turn may make** stay `Reflect.turnSpace`, the kernel's constant, which the peer cannot change either. The record now says it, `turn <cells>`, and the check refuses a record whose turn space is not the checker's (`the records' turn space is not this check's`): until now a change of the constant changed what old records replay to with nothing in them to say so. Making it a word of the guest's, lowered as the budget is, needs a space argument on every driver's turn (`runTurn` is used by requests, channels, the log, the node and the keep session) and is left out.

## D-2. A guest bounds what it holds (`q59.71`)

### What a guest holds

Between turns a guest keeps: each process's status and the names it holds (`cfg`); for each crossing it put out and that is not acknowledged, the turn it ran and kept (`asked`); the packets it sent that the peer has not counted (`sent`); the peer's packets it has accepted and not worked (`inbox`) and the peer's sends waiting for a receiver (`pending`); and its log. Each turn makes at most `turnSpace` cells (`runTurn`), but nothing bounds the sum, so a program that keeps a little each turn, or starts processes that each keep a turn's worth, ends the guest.

### The measure: a ledger, and a count when it is spent

`add-space-budget` showed that no function of a machine state measures what it holds (a closure holds its whole environment, and each definition doubles the tree), and settled on a ledger of cells *made*, pure and proved, with the runtime's count of cells *held* (`reflect_live_cells`, each object once) asked when the ledger is spent. The same is done here, one level up: the ledger is the guest's, charged entry by entry, and the count is of the whole guest.

The guest has a *hold* `H`, its own: `reflect.hold=<cells>`, or `Cross.defaultHold = 2000000`. It is not negotiated: each side's ledger is its own, and the record states it (`hold <H>`). It keeps a credit, `H` at the start. Each entry it records is charged (the table below). Then:

- the charge `c` is at most the credit: the credit falls by `c`;
- otherwise the guest counts the cells it holds, `m` (`reflect_live_cells` on the guest object, cut at the bar), and records it as an entry: when `m ≤ bar H` (`H - H / 4`, as `Space.bar`), `held m`, and the credit becomes `H - m`; otherwise `full m`, and the guest is *full*.

The entries are `[5, m]` and `[6, m]`; they emit no event and `combine` places them anywhere (`Mix.place` gives the state unchanged and no event). Counting after the entry is what lets the count see what the entry made. A count entry is not charged.

A full guest does nothing more but what it owes: it takes no packet but acknowledgements (`[2, k]`) and records their `ack`s, so that every crossing the peer took is acknowledged and the two logs still combine; a start or a send of the peer's that arrives is dropped, and that crossing stays `offered`, which the merge allows. It does no local event and puts nothing out. It goes idle and closes as any guest does. Its record ends, apart from acknowledgements, with `full m`; the check says so (`full a: entry <n>, <m> cells counted`). That is the outcome of a program that holds too much: a record, not a panic.

### The charge of an entry

| entry | charged (cells) |
|---|---|
| any but a count | `entryCells` = 32, for the note and its place in the log |
| `did (fresh i n)` | the cells `i`'s turn made |
| `did (comm i j)` | the cells both turns made |
| `did (spawn i)` | the starter's turn on `[]`, the child's start and settle, `procCells` = 128, and `codeCells prog` = 4 × the cells of the quoted program |
| `out i k` | `i`'s turn on `[]` (kept in `asked`), and the cells of the packet put out |
| `spawnIn k` | the child's start and settle, `procCells`, `codeCells prog`, the cells of the packet taken and of the `[2, k]` sent |
| `sendIn k j` | `j`'s turn on the message, the cells of the packet taken and of the `[2, k]` sent |
| `ack k i` | nothing more (the turn was charged at `out`) |
| `held m`, `full m` | nothing |

Side `a` begins the program before it records anything; that is charged to its credit before its first entry: the start and settle, `procCells` and `codeCells` of the program. If it passes the credit the first entry is a count.

"The cells a run made" is the ledger of `runSpace` (`Space.lean`): `turnSpace` less the credit left when the turn ended. `runSpace` gives no credit back, so this adds `runSpaceLeft` (same recursion, gives the credit too) and *made* variants of the channel runs: `runTurnMade`, `settleMade`, `turnMade`, `beginMade`, and `stepMade budget cfg ev`, which gives the cells made by process `i`'s side of the event (its turn) and by the other's (the child's start, the receiver's turn) apart. Each is proved to give, as its first part, exactly what `runTurn`, `settleRun`, `turnRun`, `beginRun` and `stepRun` give, so the guest's states are what they were. The cells of a packet are `cellsOf`, the cells of a data value as `Data.cells` counts them, as a walk with a list of work (a packet is small, but a quoted program started locally is not: `cross-deep` starts one 288000 deep).

What the charge does not cover, as in `add-space-budget`: that the table is at least what Lean allocates (the per-instruction table is `charge`'s; `codeCells` takes the term and code made from a quoted program as at most four cells for each cell of its data, by reading `unreify` and `compile`); garbage freed at once; the transient of a turn (bounded by `turnSpace`); and what an entry makes before it is charged.

### Where the count goes, and what the check verifies

The check replays each side's ledger. It walks the merge in the order the walk placed the entries (`combineTrace` gives that order, `tr`; `combine` is its projection, and `Walk` already carries `tr`), keeping the replay's configuration, and charges each entry from the replay's states with the same functions the guest used: at `out` the asker's turn on `[]` from its status in the replay; at a taking, the event's other half; a local event, both halves. A crossing is the guest's turn at `out` and the peer's at the taking, as in the old design's D-4. It then walks each side's entries, in its log's order, with their charges (`Hold.walk`):

- an entry whose charge passes the credit must be followed at once by a count (`the ledger was spent and not counted`);
- a count must follow such an entry (`a count where the ledger was not spent`);
- `held m` with `m` past the bar, or `full m` with `m` within it, is refused (`a count past the bar that is not full`, `full within the bar`);
- after `full m`, only `ack` entries (`an entry after full`).

So the replay reaches the same outcome as the guest wherever the ledger decides it, and the count decides only what the guest says it counted. The check cannot verify `m`: the count is a property of the guest's objects, not of the state (the replay holds both sides' processes in one configuration, shared differently). A guest that lies about `m` can say it was full when it was not, which only stops its own run, or go on when it was full, which only risks its own memory. Neither changes what the replay is.

### Memory

At any time a guest holds at most `H` cells by the ledger's account plus the cells of the one entry being made, which is at most two turns (`2 × turnSpace`), the packets (each at most 6000 bytes), and, for a local start, the code of the quoted program it starts, which its payload bounds (a payload is at most `4 × turnSpace` written, `runTurn`). At the default, `H + 2 × turnSpace` is 10 million cells, 240 MiB at 24 bytes a cell, with the walk's table and stack for a cut of 1.5 million (16 MiB and 12 MiB) on top, against the 360 MiB of the image's `mmap` area. The default is checked against the worst programs on the image (below) and recorded in `unikernel/README.md`. `cross-deep.hom` holds more than that by design (data 960000 deep and a program 288000 deep, and the code of the program): its run is given `reflect.hold=16000000`.

### What the peer can make a guest hold

The ledger charges what the guest's program does. What the peer sends arrives before it is an entry, so two plain limits cover it: a guest puts out at most `outLimit` = 64 crossings that are not acknowledged (a start or send that would be the 65th waits: the guest's choice, as when a send is put out in the old design's D-3, and recorded by the entries it produces), and accepts at most `queueLimit` = 128 packets into `inbox` and `pending` together; a packet past that is not accepted (`got` does not count it) and the peer sends it again later. An honest peer never has more than 64 crossings out and 64 acknowledgements owed, so it never meets the limit. A packet is at most the 8 KiB a batch's stream carries. Packets the peer has counted are dropped from `sent`; a peer that never counts makes `sent` grow only with entries this guest made and charged.

The limit of 64 crossings out can leave a program stuck that another schedule would finish (64 sends on names whose receivers on the peer wait for a 65th first). The old design already admits that a guest's choices can do that.

## D-3. What the check compares (`q59.69`)

### A root on each process line

A process line becomes `<status>; holds <names>; root <hex>`: `root` is the Blake3 hash of the byte form (`Wire.write`) of `[names held, status]`, with the status as data: `[0, function, payload]` for a waiting process (the function in the data form of a machine value, `Wire.valueData`), `[1, value]`, `[2, i]` or `[3]` for one finished with a value, unbound, or wrong. The replay computes the line of its process the same way, and the check compares lines as it does, so the root is compared wherever a line is. The status part of a line prints a payload or a result only when it is at most 4096 written (`Data.writes`); a larger one is printed as `a payload of more than 4096` or `a result of more than 4096`, and the root covers it. (Lines are bounded so that a record is bounded: with the ledger's charges it fits in 16 MiB, the guest's record buffer.)

The form of a function is a tree: each value it captured is written where it is held, so it can be far larger than what is held (`Wire.fitsValue`). A root is made only when the process's form fits a room: each process may use `procRoom` = 1000000 units of `Wire.valuesFit`, and a side `sideRoom` = 8000000 over its processes in local order; a process that does not fit, or that comes after the side's room is used, has `root none`. Trying a process uses its room whether it fits or not, so a side costs at most `sideRoom` units however many processes it has. The guest and the replay run the same rule on the same states and agree on which processes are `none`; a guest cannot choose `none` for a process the replay can root.

Why not `Wire.save`'s root. `same_root` is about `save` of a piece, and the task suggested it. `save` cuts a piece with `cut`, which recurses on the native stack once for each level of a list and of nesting, and `pieceItem` does too; a process that finished with a list of 100000 items, or `cross-deep`'s data, would end the guest in a full stack (`homoiconic-q59.72`). `Wire.valueData` and `Wire.write` are walks. The root here has the property that matters for comparison, and it is not a theorem to state: equal states give one root, because it is a function of the state; one root names one state, because the byte form reads back to its value (P4, tested) and Blake3 names one byte string (D5). Nothing fetches pieces under it, so `save`'s pieces add nothing.

### Acknowledgements in the order of the takings

A guest records `ack k` when the peer's `[2, k]` arrives; the peer sends `[2, k]` at the entry where it took crossing `k`, packets are numbered and taken in order, and `inbox` is worked in order. So in two honest records, the crossings guest `s` acknowledges, in its log's order, are exactly the crossings of `s` that the other guest took, in the other's log's order, and every crossing taken is acknowledged before the two close (the old design's D-2). The check now requires it, in both directions (`the acknowledgements of b are not the order a took them in`).

It closes a real gap: until now `a`'s record of one run and `b`'s record of a run with the takings the other way combined and were accepted (`kernel/CrossCheck.lean`, "the acknowledgements in another order still combine"). The two records describe two different runs and their pair is not a run either guest made. It also fixes, for each guest, the order of the other's takings of its crossings against its own entries: a guest cannot reorder the peer's deliveries to it in its own log without contradicting the peer's signed record.

### What a lying guest can and cannot do afterwards

Each guest signs only its own record, and nothing attests what a guest ran. So the strongest claim is about one guest that lies, checked against the signed record of one that does not.

A record of guest `s` that the check accepts beside an honest peer's is, on `s`'s side:

- a log that, with the peer's log, combines and replays as a run of the one-machine network (`accepted_network`, unchanged);
- crossings, takings and acknowledgements that agree with the peer's at every crossing: the same crossing numbers out and taken (`combine`), and the peer's deliveries to `s` in the peer's order (acknowledgement order);
- a final state of each of `s`'s processes, its line and, where it fits the room, its root, that is exactly what that replay ends with;
- counts placed where that replay's ledger was spent, with outcomes consistent with the bar;
- the budget the peer ran with, at most `s`'s stated limit, and the checker's turn space.

So `s` cannot:

- hand over a log with a final state that is not that log's (the lines and roots are the replay's); in particular not the q59.69 lie, a log with a turn dropped or repeated, reported with the state the guest actually reached;
- take a crossing twice, take one that was not put out, leave one taken unacknowledged, drop one it took (`combine`);
- acknowledge the peer's takings in another order than the peer took them, or pair its record with a record of another run of the peer's;
- run with another budget than the peer's, or with another turn space;
- say it was full, or counted, where its ledger was not spent, or go on past `full`.

And `s` can still:

- hand over a record of a *different run* of the same program, made whole: its own local events, their interleaving with the crossings, the choices of which pending send to take and when to put a request out, and which of its processes it says asked, all other than what it did, provided the result is a run that agrees with the peer at every crossing, and with lines and roots computed for that run. It can compute those itself: its processes depend only on its own entries and the packets it was sent. The check cannot tell this from the run the guest made; a signature says who handed a record over, not that it is true.
- choose the counts it reports, within where the ledger puts them: call itself full early, or say `held` with a small count. This changes whether its run went on, not what the run is.
- state its own limit and hold as it likes, as long as the budget is at most the limit.
- report `root none` only where the replay also cannot root the process; for such a process only its line binds the state.
- stop: give no record, or a record that the peer's does not combine with (the old design's D-2, liveness).

Two guests that lie together can hand over any run of the program: the check has nothing honest to hold them to.

## D-4. The record's form

A record is text, one item per line, signed whole by its guest (`add-entity-keys`):

```
form 2
me <entity name>
peer <entity name>
budget <steps every turn ran with>
limit <this guest's own step limit>
turn <cells a turn may make: Reflect.turnSpace>
hold <this guest's hold, cells>
entry [[0, parent, order], body]      -- bodies [0, event] [1, i, k] [2, k] [3, k, j] [4, k, i] [5, m] [6, m]
...
head <entries> <name of the last>
proc <status>; holds <names>; root <hex|none>
...
```

`form 2` is new and marks the form: the old form had no such line and is refused (`record a: not of form 2`). Every header line is required. The byte form of packets and batches does not change: a batch is still `[flag, got, budget, [[seq, packet], ...]]`, and only what the budget field means changes (the sender's budget as it stands, a ceiling on the receiver's, never a floor).

## D-5. The exports and the image

- `reflect_cross_start(flags, limit, hold)`: the limit and hold as above; 0 means the default.
- `reflect_cross_give(g, program, length, budget)`: as now; the budget is a ceiling.
- `reflect_cross_work(g)`: works with the runtime's count of the guest (`reflect_live_cells` on the Lean guest object, cut at the bar of its hold). `kernel/CrossCheck.lean` runs under Lean's evaluator, which cannot call it; there a guest's count is a parameter, the ledger alone (a count that always answers "too many", as `Space.ledger`), or a fixed number to make `held` entries.
- `unikernel/net.zig`: the words `reflect.budget=<steps>` (1 to 2^64 − 1) and `reflect.hold=<cells>` (a whole number), each at most once, only on an end of the crossing; the record buffer grows from 256 KiB to 16 MiB.
- `unikernel/cross-check.zig`: its record buffers grow to 16 MiB.

## D-6. Proved, tested, assumed

Proved, in `kernel/Reflect/CrossingProof.lean` and `kernel/Reflect/HoldProof.lean`, stated in `kernel/CrossingContract.lean` with `#print axioms`, no `sorry`, no new axiom:

- `accepted_network`, `combine_merged`, `merged_exact`, `merged_once`, `Walk.once`: as stated now, with the two new entries in `Note`.
- `combineTrace_walk`: the order the check charges in is a `Walk` of the two logs, so each side's entries are charged in its log's order (`Walk.exact`).
- `runSpaceLeft_fst`, `runTurnMade_fst`, `settleMade_fst`, `turnMade_fst`, `beginMade_fst`, `stepMade_fst`: the measured runs are the runs the replay and the guest made before.
- Of `Hold.walk`: when it accepts a side, every stretch of entries from the start or a count up to the next count charged, without its last entry, at most the credit the stretch began with (`hold_stretch`); a count it accepts as `held` is at most the bar and the next stretch begins with `H - m` (`hold_count`); after a `full` it accepts only acknowledgements, and its count is past the bar (`hold_full`).

Tested, not proved: the guest's step (budgets, the ledger, the limits, the roots); that the replay's charges are the guest's; reading a record; the image.

Assumed: Blake3 names one byte string and the byte form one value (D5, D7); the runtime's count (`add-space-budget`); that the charge table covers what Lean allocates; the signature; that a name cannot be forged across machines.

## D-7. The checks and their controls

`kernel/CrossCheck.lean` (two guests in one process) and `unikernel/check-wire.sh` (two real guests). Each new refusal is asserted with its reason, and `kernel/cross-controls.py` undoes its check in a copy of the kernel and requires the test to fail.

| test | where | refused with / ends in | control |
|---|---|---|---|
| the peer announces a huge budget in a batch | Lean | `b`'s record says `budget 100000`, its own limit | `take` takes the peer's budget |
| the guest given the program asks a huge budget, the other's limit is lower | Lean, wire | both records `budget <the lower limit>`, accepted | side `a` does not wait to hear / does not take the peer's budget: the budgets differ |
| a budget above its own limit | Lean, wire | `record b: its budget is above its own limit` | the comparison removed |
| another turn space | Lean | `the records' turn space is not this check's` | removed |
| a record of the old form | Lean | `record a: not of form 2` | removed |
| a program that holds more and more across turns (`examples/cross-grow.hom`) | Lean, wire | accepted, `full a: entry …` on the image, no panic; `INTERNAL PANIC: out of memory` with `reflect.hold=18446744073709551615` | the guest's ledger check removed (Lean); the hold set to its largest (image) |
| processes started on the peer that each hold a turn's worth (`examples/cross-fan.hom`, `spawn=far`) | Lean, wire | accepted, `full b: …` | as above |
| counts recorded (a fixed count in Lean) | Lean | accepted, `hold a: … counts` | — |
| a count moved, dropped, inserted where nothing was spent; `full` within the bar; an entry after `full`; re-signed | Lean | each its `hold a: entry n: …` reason | each rule of `Hold.walk` removed |
| a different run, re-signed, with the state it had (a local race whose two deliveries are swapped, `examples/cross-hidden.hom`) | Lean, wire | `process 0 (a 0): reported …; root X, replayed …; root Y` | the root left off the line |
| one guest's record of one delivery order with the other's of the other | Lean, wire | `the acknowledgements of b are not the order a took them in` | the order not compared |
| a different run made whole: the swapped log with the replay's lines and roots | Lean | accepted (what a lying guest can still do) | — |

## D-8. Open, not in this change

- More than two guests (`Side` is two-valued, `Mix` holds two tables): a new bead.
- A turn's space as the guest's own word (D-1).
- That every pair of honest logs combines, and a theorem about a guest's step (the old design's D-7, `homoiconic-q59.68`).
- A count that is a function of the state (`homoiconic-q59.74`), which would let the check verify the counts.
