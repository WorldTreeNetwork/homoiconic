# What is proved

A record of what the Lean proofs say, how they got there, and what they leave
out. The exact statements are in `kernel/ReflectContract.lean`,
`kernel/MachineContract.lean`, `kernel/RequestContract.lean` and
`kernel/StoreContract.lean`, and for the byte form in `kernel/WireCheck.lean`;
the requirements are in `openspec/specs/`.
Written 2026-11-10, after `add-operation-tables`; updated 2026-11-10, after
`add-requests`, 2026-11-11, after `add-state-store` and `add-wire-bytes`, and
2026-11-12, after `add-kept-state`, 2026-11-17, after `add-data-kinds`, and
2026-11-25, after `homoiconic-q59.72` (walks).

## In one sentence

The language proves its own interpreter correct on every program, and keeps
that proof when the set of processor operations changes.

## How the quote proof got here

**2026-11-08: correct, except for quote.** The first kernel, `Circular`, had
`quote` as a term, but direct evaluation had no rule for it. A Lean function
beside the language turned programs into data, with a Mogensen–Scott encoding
into lambdas. The theorem `metacircular` (commit `46048e9`) said the
interpreter written in the language agrees with direct evaluation, for
programs that contain no quote. A program could not build, hold or inspect
another program. Code was data in Lean and not in the language.

**2026-11-09: the side condition goes.** Data became primitive: numbers and
arrays. In the library `Reflect` a literal holds data, and `reify` maps every
term to data. The interpreter takes that data apart with an ordinary case
expression. `reflective` (commit `4ec21ae`) has no condition on the program:

> `p` evaluates to `o` exactly when the interpreter applied to `p`'s data form
> evaluates to `o`'s data form.

**2026-11-10: one kernel, and operations.** `Circular` was deleted (`26a88ca`).
Every theorem now begins `∀ [Ops]`: it holds for every table of operations
(`f89c88a`). The interpreter runs an operation by using the same operation, so
it never looks at which table is in force.

**2026-11-10: requests.** A program can ask the outside for something and
continue from the answer (`b5885e3`, `c14f63a`). A request is not a new
outcome: it is a function value that holds a payload and the rest of the
program, and a driver outside evaluation answers it from a list. Nothing in
the language, evaluation, the interpreter or the machine changed, and no
earlier theorem statement changed. The driver is defined once over any way of
evaluating, so the agreement of the interpreter and the machine with direct
evaluation carries over to whole runs of requests and answers.

**2026-11-11: stored state.** A running program's state can be held in pieces
and fetched on first use (`f022a06`, `9348a9d`). A piece is a number, an empty
list, a pair, a function, or a reference to another piece. A lazy machine runs
a partial state, fetches a piece when a step first looks at it, and pauses
when the store lacks it. The kind of reference is a parameter, as the
operation table is. Nothing in the language, evaluation, the interpreter or
the machine changed, and no earlier theorem statement changed.

**2026-11-11: a byte form.** Data, programs and machine values can be written
as bytes and read back (`8218a07`, `aafab3c`). The format is the part of dCBOR
that numbers and arrays need, with CBOR tag 2 for numbers of 2^64 and above.
By decision D7 the format is tested, not proved. One statement about it is
proved: reading a program's data form gives the program. Nothing in `Reflect`
changed.

**2026-11-12: kept state.** A waiting program can be kept on disk and answered
in a later process (`9d83f8a`, `edaee36`). A reference is the Blake3 hash of a
piece's bytes, and Blake3 is a Lean definition. A piece has a byte form, and
saving cuts a value by size. A session runs one turn against a store it is
handed piece by piece, and the command `host/out/keep` keeps the pieces as
files. Nothing new is proved. The hash, the byte form of a piece, saving and
the session are tested.

**2026-11-17: text and names.** `Data` gained two kinds, text and channel
names (`046ab3f`, `b854f38`). The interpreter tests a value only with its own
`case` and builds its answer with its own `succ`, `cons` and `prim`, so each
kind is seen by `case` as a number or as a list and goes `wrong` exactly where
that view does: a name is seen as its number, a text as the list of its code
points. `Direct` gained twelve rules and no existing rule changed. `interp`,
`evalTerm`, `Interpreter.lean` and `Correctness.lean` were not edited, and
`reflective`, `reflective_coverage`, `reflective_env` and `tower` were proved
again, with the same statements, for the wider `Data`. So were the machine,
store, request, log and node theorems: their contract files were checked
unedited and print the axioms they printed before. One theorem is new,
`Network.held_nodup`. Before `ReflectContract.lean` could be checked, an early
gate, `kernel/InterpGate.lean`, imports `Reflect.Correctness` alone and
restates the four interpreter theorems with their axioms.

## The definitions

- **Data** is numbers, arrays, text and names. A text is a list of Unicode
  scalar values, seen by `case` and `cons` as the list of its code points; a
  name carries a number, seen as that number by `case`, `succ` and the
  operation number of `prim`.
- **Terms** are variable, function, application, literal, successor, cons,
  case on data, and operation.
- **`reify`** turns any term into data.
- **Evaluation** is defined twice: as a relation, `Direct`, and as a function
  with fuel, `evalFuel`.
- **Outcomes** are a value, an unbound variable, or `wrong`. A program that
  runs forever has no outcome.

## The theorems

All hold for every operation table. All rest on Lean's three standard axioms
and nothing else.

### Evaluation

| Theorem | Says |
|---|---|
| `direct_deterministic` | A program has at most one outcome |
| `direct_iff_evalFuel` | The relation and the runnable function agree |

### The interpreter written in the language

| Theorem | Says |
|---|---|
| `reflective` | A program gives `o` exactly when the interpreter on the program's data gives `o`'s data |
| `reflective_coverage` | The interpreter only ever produces the data form of a real outcome |
| `reflective_env` | The same for open terms in any environment |
| `tower` | Interpreters stacked `k` deep still agree |

### The stack machine

| Theorem | Says |
|---|---|
| `machine_correct` | A program gives `o` exactly when the compiled program halts with `o` |
| `machine_exact` | Anything the machine halts with is the outcome of the program |
| `machine_never_halts` | A program with no outcome never halts the machine |
| `machine_never_faults`, `machine_never_faults_until`, `machine_never_faults_priced` | A compiled program never reaches the machine's fault state, at any step count or budget, whether or not it halts |
| `run_add`, `run_halted` | Pausing and resuming equals running straight through; a halted machine stays halted |
| `runUntil_eq` | The early-exit loop the host uses equals the proved one |
| `decompile_compile` | Bytecode converts back to the exact term |
| `depth_bound` | Stack depth plus pending frames grows by at most one per step |
| `run_cycle`, `runPriced_cycle` | A run that comes back to a state it held stays in its first `a + p` states, at any step count or budget |
| `runSpace_run`, `runSpace_priced`, `machine_never_faults_space`, `machine_exact_space` | A run with a space limit takes `run`'s steps and, when it is not stopped for space, is the priced run; it never faults, and what it halts with is the outcome of the program. For every count a host supplies |
| `runSpace_full`, `runSpace_within` | A run is stopped for space only when the cells made would pass the credit it began with, so a run that stays inside its ledger is the priced run whatever the count |
| `trail_held`, `trail_last`, `runSpace_ledger`, `runIn_ledger` | Every state a space-limited run is in was reached from its start by steps that made no more cells than its credit, or from a state it counted at no more than three quarters of its limit by steps that made no more than the rest; with no count, the steps made at most the limit |
| `runTurn_reach` | Where a driver's turn is left, `run` gets to: the driver theorems hold of turns under a space limit |
| `runPriced_eq_within`, `runSpace_eq_within`, `stepCostWithin_eq`, `arithCostWithin_eq` | What runs asks each charge within the fuel left, and is the priced run and the space-limited run; for `arith`, `equal`'s charge found within a cap is the charge, or more than the cap (`homoiconic-q59.73`) |
| `runPriced_unit` | With a table whose every charge (`cost`, `work`, `reach`) is one, a priced run is `runUntil` |
| `omega_cycle`, `forever_cycle`, `forever_cycle_interp`, `forever_bounded` | A tail loop keeps no frame per call: `omega` and `examples/forever.hom` repeat a state exactly, forever also through one interpreter, so a run of any budget holds one of finitely many states |

### Requests

A run is a program driven against a list of answers: the requests it makes, in
order, and how it ends (finished with an outcome, or waiting on a request).

| Theorem | Says |
|---|---|
| `interact_deterministic` | The requests a program makes and how it ends are fixed by the program and the answers |
| `interact_resume` | A waiting program continued with an answer is the program run from the start with that answer added |
| `interact_extra` | A program that finished is not changed by more answers |
| `interact_reflective` | The interpreter, driven on data, makes the same requests in the same order and ends the same way |
| `interact_coverage` | Every interpreted run is the data form of a run of the program |
| `interact_machine` | The machine makes the same requests and ends the same way |
| `interact_machine_exact` | Whatever the machine's run ends with is the compiled form of the program's ending |
| `converse_finished`, `converse_waiting` | What the executable driver reports as finished or waiting is a run of the program by direct evaluation |

### Channels

Several programs run as processes. A schedule is a list of events; a
configuration is every process, the names each holds, and the names made.

| Theorem | Says |
|---|---|
| `network_deterministic` | The configuration a program reaches is fixed by the program and the schedule. New names and outside answers are events of the schedule |
| `Step.comm_held` | A send and a receive meet only on a name both processes hold |
| `Step.held_from` | After an event a process holds a name only if it held it before, or the event made it for that process, or the event is a message to it, or a start, from a process that held it |
| `Network.held_issued` | Every name a process holds was made by an event of the schedule |
| `Network.held_nodup` | No process holds a name twice. It rests on an invariant, `Config.Tidy`: every held list has no repeat and is within the names made |
| `network_machine`, `network_machine_exact` | The machine runs a schedule exactly as direct evaluation does |
| `network_reflective`, `network_interpreted_exact` | A schedule leads the program to a configuration exactly when it leads the run in which every evaluation is done by the interpreter on data to that configuration's data form, and the interpreter has no other runs. The scheduler is outside the interpreter, and one level of interpretation is covered |
| `replay_true`, `auto_true` | The events the executable scheduler reports as done, and the configuration it reports, are a run of the program by direct evaluation, however the run stopped |

### The log

A VM is a program and the identifiers of the log entries it has acted on. A
log is a list of entries, each an identifier and an answer. An entry that is
read is sealed: its identifier is the name `key` gives to its mark and its
answer together. The kernel's `key` is a Blake3 hash.

| Theorem | Says |
|---|---|
| `log_deterministic` | The state of a VM is fixed by its program and its log |
| `log_prefix` | The state after a log is the state after any first part of it, carried on through the rest |
| `log_again` | Handling an entry that is already in the log leaves the state as it is |
| `log_redeliver`, `log_once` | An entry delivered again changes nothing; a log does what its first deliveries do, in their order |
| `log_restart` | A state reached by a first part of the log, given the whole log, reaches what the whole log reaches from the start |
| `log_interact` | A VM's run is a run of its program by the request driver, against the answers of the first deliveries |
| `log_machine`, `log_machine_exact`, `vm_true` | The machine handles a log exactly as direct evaluation does, and a state the executable fold reports is the program's |
| `sealed_same`, `sealed_first` | When `key` gives different names to different data: two sealed entries with one identifier are one entry, so no entry of a sealed log is passed over for a different one |

### Nodes

A node is several processes and the identifiers of the ops it has acted on. An
op is an event with an identifier.

| Theorem | Says |
|---|---|
| `node_deterministic`, `node_prefix` | The node a program reaches is fixed by the program and the log, and the node after a log is the node after any first part carried on through the rest |
| `node_again`, `node_redeliver` | An op already in the log changes nothing |
| `node_restart` | A node reached by a first part of the log, given the whole log, reaches what the whole log reaches from the start |
| `node_network` | A node's processes are where the schedule of the log's first deliveries leads the program, so the channel theorems hold of them |
| `node_machine`, `node_machine_exact`, `node_true` | The machine applies a log exactly as direct evaluation does, and what the executable node reports is true however it stopped |
| `sealed_op_same`, `sealed_op_first` | The same two statements for ops, whose identifier is the name of the mark and the event as written |
| `plan_step`, `step_plan` | An event happens exactly when the runs of its plan end somewhere and the plan gives the next configuration from there |

### Crossing

A run on two guests. Each guest logs its local events and its halves of the
crossings; `combine` walks two logs into one schedule, and `accept` replays it.
Since `harden-crossing` the two guests agree on a step budget and a turn
space, a guest keeps a ledger of what it made (`Reflect.Hold`), and the check
replays in the order the merge placed the entries (`traceRun`), charging each
as its guest did.

| Theorem | Says |
|---|---|
| `accepted_network` | A record the check accepts is a run of the one-machine network from the program: the schedule the two logs make leads the program, by direct evaluation, to a configuration whose compiled form is the one the check reports, for every turn space and budget the guests agreed on. This is `replayIn_true` applied to the merge; the check accepts by replaying |
| `combine_merged` | The walk does only what the table of placements allows (`Merged`, a relation defined apart from the order the walk chooses) |
| `merged_exact` | A walk keeps each guest's log whole and in its order |
| `merged_once`, `Walk.once` | In a walk no crossing is taken twice |
| `combineTrace_walk` | The order the check replays in is such a walk, and its events are the schedule `combine` gives |
| `combine_complete` | The greedy walk is complete: two logs that have any schedule the table allows combine, so `combine` refuses only when no order of the entries is allowed |
| `replay_agrees`, `Walk.replay` | Take two logs that are each what a guest's log allows read alone (`SideRun`: each entry against that guest's own processes, with the machine's runs), every crossing taken as the packet its guest made for it. Any walk the table allows over them replays to the end; when they combine, `accept` accepts them and what the replay reaches is, at each guest's places and in order, that guest's processes |
| `honest_combine`, `honest_accept` | Two guests that follow `Surface.Cross` (`Reach`), where nothing is in flight (`Quiet`): their logs combine, and once `a` has begun, `accept` (the merge and the replay; the ledger walk and the record's text are not in it) accepts them with the budgets `a` ran with and replays to the processes each guest holds |
| `honest_budget` | A guest that has run anything runs with the other guest's step budget and turn space, in every state reached |
| `honest_acks` | Where nothing is in flight, each guest's acknowledgements are in the order the other took its crossings: the comparison the check makes |
| `traceRun_sched` | The check's replay, which charges each entry, is `schedIn` on that schedule when it runs every event: `accepted_network` speaks of what the check ran |
| `runTurnMade_fst`, `settleMade_fst`, `turnMade_fst`, `beginMade_fst`, `stepMade_fst` | The measured runs a guest and the check charge with are the runs (`runTurnIn`, `settleIn`, `turnIn`, `beginIn`, `stepIn`); `runSpaceLeft_eq_within` runs them with each step's charge capped by its fuel |
| `hold_stretch` | In a side's ledger the check accepts, the entries from the start or a count up to the next count charged, without the last, at most the credit the stretch began with |
| `hold_count` | A count the guest went on from is at most three quarters of its hold, and the next stretch begins with the hold less the count |
| `hold_full` | After `full` come only acknowledgements, at most `outLimit` |
| `hold_entries` | A side the check accepts has at most `entryLimit + outLimit + 2` entries |

The channel soundness theorems (`settleIn_sound` to `replayIn_true`) hold for
every turn space; the old statements at `turnSpace` follow from them.
Axioms: `propext`, `Quot.sound`, and `Classical.choice` for
`runSpaceLeft_eq_within`, `combine_complete`, `replay_agrees` and the four
`honest_` theorems (`kernel/CrossingContract.lean`,
`kernel/GuestContract.lean`).

The `honest_` theorems are about a model, `kernel/Surface/CrossModel.lean`: a
guest changes only by the functions the image calls (a step of `Guest.work`
with any count, `give`, `batch`, `take`), and a batch a guest takes is one the
other made at some earlier time. A batch may be lost, taken twice, or taken
after a later one. A batch is taken as the data it was made from. What is
proved of every state so reached is `Reach.inv`: each guest is what its own
log says, each packet worked is one the other made, in order and once, and the
entries in the order they were recorded are a path the table allows. The
theorems are read off it, three of them where nothing is in flight. Mid-run
two honest logs need not combine: a crossing taken whose acknowledgement is
not yet worked is refused by the merge (`kernel/CrossCheck.lean` shows one).

Not proved of a guest: that two guests that have closed have nothing in flight
(it rests on batches being answered one exchange at a time, as
`unikernel/net.zig` does it), and that a guest that ran nothing ends with the
other's budgets, which the check compares (`homoiconic-q59.85`); that the
replay's charges are the guest's, so that the ledger walk accepts
(`homoiconic-q59.86`); that a batch's bytes and a record's text read back
(`homoiconic-q59.87`). These are tested by `kernel/CrossCheck.lean` and on two
real guests by `unikernel/check-wire.sh`. A guest's counts (`held m`,
`full m`) are its runtime's and are not verified: the check verifies where
they are, not what they say. What a guest that lies can still hand over is in
the design of `harden-crossing`, D-3.

### Stored state

A store holds pieces under references and may lack any of them. A piece
resolves to a value when following every reference gives that value. These
hold for every operation table and every kind of reference.

| Theorem | Says |
|---|---|
| `saved_resolves` | A state held whole resolves to itself |
| `cut_resolves` | A stored piece can be replaced by its reference, and what resolves is the same |
| `RState.mono` | A state that resolves still does when the store holds more |
| `Unf.unique`, `resolve_unique` | A piece resolves to one thing, and a partial outcome to one outcome |
| `lazy_simulates` | For every number of plain steps, the lazy machine with the whole store reaches a state that resolves to the plain machine's state |
| `lazy_complete` | The lazy machine halts with what the plain machine halts with |
| `lazy_sound` | Under any part of the store, what the lazy machine halts with is what the plain machine halts with |
| `lazy_pause` | A run pauses only on a reference the store lacks, and under a store that holds more, the run from the start passes through the paused state |
| `lrun_mono` | More pieces change no run that did not pause |
| `lazy_agree` | Two stores that agree wherever both hold a piece give the same result from the same state, when both runs halt |
| `lazy_program` | A program run through any store has exactly the outcome direct evaluation gives it |
| `lazy_turn_complete`, `lazy_turn_sound` | A turn of the request driver from a stored continuation is a turn of the machine |

### The byte form

One theorem. It does not depend on an operation table.

| Theorem | Says |
|---|---|
| `Reflect.unreify_reify` | Reading a program back from its data form gives the program: `unreify (reify t) = some t` for every `t` |

It is checked, with its axioms printed, in `kernel/WireCheck.lean`, not in a
contract file. The reader and writer of bytes are not proved. They are tested
by `WireCheck.lean` (decision D7): the RFC 8949 appendix A examples that are
numbers, text strings or arrays, names under tag 39, text that is not UTF-8, each integer width at its edges, twenty-six spellings that
must be refused, every string of one or two bytes, eleven programs written,
read back and run from their bytes, and a waiting run kept as bytes and
continued.

### Walks

What the compiled kernel runs in place of a function that would recurse once
for each level of nesting (`homoiconic-q59.72`). Each `@[csimp]` theorem says
the walk is the function, so the compiler runs a loop over a list of work on
the heap and no definition a theorem mentions changed. Restated, with axioms
printed, in `kernel/WalkContract.lean`.

| Theorem | Says |
|---|---|
| `reify_eq_walk`, `unreify_eq_walk` | Quoting a program and reading it back are walks |
| `comp_eq_walk`, `decomp_eq_walk` | Compiling and reading code back are walks |
| `mentions_eq_walk` | Finding the names a value hands over is a walk |
| `Data.same_iff` | `Data.same x y = true ↔ x = y`; it is `==` on data and operation 5 |
| `Wire.valueData_eq_walk`, `Wire.codeFits_eq_walk` | A machine value's byte form, and what it is counted at, are walks |
| `Wire.Code.same_iff` | `Code.same a b = true ↔ a = b`, the comparison in `blockTerm` |
| `Surface.renderData_eq_walk` | The printer is a walk |
| `Surface.decimal_eq_go`, `decimalGo_eq` | A number is printed by halves split at a power of ten, and the digits are `Nat.repr`'s (`homoiconic-q59.64`) |
| `Surface.Read.digitsValue_eq_split`, `takeWhileB_eq_walk` | The reader reads a number's digits by halves, and a token as a tail walk |
| `Wire.bigBE_eq`, `Wire.pushBig_eq` | A bignum's bytes are read and written by halves, and are `takeBE`'s and `pushBE`'s |
| `Surface.Cross.chain_eq_walk`, `numbers_eq_walk` | A crossing record's chain and a packet's names are loops |

The derived `==` on data was opaque (a `partial` function), so operation 5
could not be proved to decide anything and nothing was proved of it;
`Data.same` replaced it as the instance, and is proved. That it answers as
the derived one did is tested: `host/check.sh` gives the same text before and
after.

### Kept state

Nothing new is proved. What a kept program rests on is already in
`kernel/StoreContract.lean`: where the cuts go cannot change what a program
computes (`saved_resolves`, `cut_resolves`, `lazy_complete`, `lazy_sound`), a
missing piece is a pause (`lazy_pause`), and a turn from a stored continuation
is a turn of the machine (`lazy_turn_complete`, `lazy_turn_sound`). Those hold
for every kind of reference, so they hold for hashes.

Assumed: two different pieces do not share a hash (decision D5 of the vision).
Given that, a reference names one piece for ever, which is the hypothesis the
store theorems already state on the stores they compare. No theorem states
collision resistance, and no axiom is added.

Tested, not proved (`kernel/KeepCheck.lean`, `host/check.sh`):

- Blake3 gives the hash of each of the 22 official test vectors that ship in
  Zig's standard library, from 0 to 102,400 bytes. Where `b3sum` is
  installed, `check.sh` also compares every stored file's name with it.
- Eight programs are stopped at three points and saved, cut at 256 bytes and
  at every value. Every stored piece is named by its hash and reads back to
  the same bytes, and the lazy machine continues from the stored pieces to
  the plain machine's result.
- A number larger than the size is stored on its own, and cutting at 0 stores
  every part.
- A result that sits behind 70 references is found.
- Three turns, each a new session over the pieces the last one left, give what
  one run against both answers gives.
- The command keeps `examples/keep.hom` across three processes, answers a root
  twice, exits 3 with a piece missing, and refuses a piece with a byte added.

The session that joins the machine runs, `Surface.Keep.advance`, repeats the
logic of `Reflect.driveRun` for one turn, on the lazy machine. `driveRun` has
theorems; `advance` is tested against it.

## Why these proofs can be trusted

- **Both directions.** The main theorems are "if and only if". Errors map
  across exactly, and a program that never finishes never halts the machine.
- **Nothing assumed.** No `sorry`, no added axiom. The contract files print
  each theorem's axioms on every check.
- **The contract cannot rot.** The four contract files restate each theorem
  with its exact signature, so a weakened theorem fails to compile. They do
  not import an operation table, so nothing is proved for one table only.
- **New operations cost no proof.** Adding a table changes no lemma.
- **The fast path equals the specification.** What the host runs is the
  machine with the early-exit loop, and both are proved equal to `Direct`.
  Where the compiled kernel runs a walk instead of a definition, a `@[csimp]`
  theorem says they are equal; no `implemented_by` is left in the kernel.
- **Compiled code is still data.** Bytecode decompiles to the term it came
  from.
- **Read by another model family.** Each change went to an outside reviewer
  before it was folded. Reviews have sent work back eight times.
  `add-state-store` was accepted on first reading. `add-wire-bytes` and
  `add-kept-state` were each sent back once, with two required fixes; all
  were made before the fold. `add-unikernel-image` was sent back once, with
  six required fixes, all made before it was accepted. `add-data-kinds` was
  sent back twice in design, with three required fixes and then one, and its
  implementation was accepted with none.

## What the proofs do not cover

- **Memory.** A step budget bounds the stack and the frames (`depth_bound`),
  and a tail call keeps no frame, so a tail loop runs in constant memory
  (`forever_bounded` for `examples/forever.hom`, measured at about 7 MiB at
  every budget, `homoiconic-q59.65`). The environments, closures and data a
  run keeps are bounded by a space limit, and what is proved of it is about
  cells made, not cells held (`trail_held`, `homoiconic-q59.67`). Three things
  between that theorem and the machine's memory are not proved. That `charge`
  covers the objects a step allocates is checked by reading `step`. That a
  state holds no more than it began with and what was made since is true of
  memory and cannot be stated: the state is a tree, and a part held in two
  places is not marked as one (counted as a tree, a program of 20 definitions
  is 20 million cells for 152 objects). And the count a run asks for when its
  ledger is spent is the runtime's, a walk of objects by address in C
  (`reflect_live_cells`), which is not a function of the state; the theorems
  hold for every count, so they hold of that one, but past its ledger a
  run's outcome is a fact about one build of the kernel. What a cell is in
  bytes, the allocator, the walk's own table and the printer are measured
  (`unikernel/README.md`). P3 as stated, a bound linear in steps, is false:
  one step of `cons` onto a text makes cells without bound. The lazy machine
  of a kept session has no space limit (`homoiconic-q59.70`). A guest of a
  crossing bounds what it holds by a ledger of what it made and the runtime's
  count when the ledger is spent (`harden-crossing`, `hold_stretch`). How deep data, programs, code and functions nest is
  bounded by memory and the space limit, not by the native stack: every
  function the compiled kernel runs on them is a walk proved equal to its
  definition (see Walks, `homoiconic-q59.72`). The source reader is not: it
  recurses on how deep a source nests, and an image reads only the source
  built into it.
- **Reader, renderer, Zig host.** Tested, not proved. That the printer the
  compiled kernel runs is `renderData` is proved (`renderData_eq_walk`); what
  `renderData` prints is tested.
- **Running through the interpreter, and text.** `reflect_interp` runs the
  closed term `interp` on the machine, so what runs is covered by the
  interpreter and machine theorems. Reading the answer back through the
  levels of an outcome's data form (`unreifyOutcome`, `unlift`) and writing a
  text raw (`renderMOutcomeText`) are tested by `host/check.sh` and
  `kernel/Surface/Check.lean`, not proved. A string literal is a text; that
  rendered text reads back is tested, not proved.
- **Text and names.** The twelve rules are proved through the interpreter,
  machine and store theorems. Not proved, and tested: the three functions of
  `kernel/Reflect/Text.lean` (that `codes` agrees with a `case` walk is
  checked in `ReflectRun.lean`), operations 7 and 8, the UTF-8 boundary in the
  byte form and the reader, tag 39, that a text is stored whole, and that a
  held name is printed and kept as a name. Text is not normalised. A state
  kept before names were data is not migrated.
- **The machine image.** `unikernel/out/reflect.elf` runs the same compiled
  Lean objects as the Linux process, and nothing under them is proved. Its
  trusted base is the boot code (`unikernel/boot.S`), the Zig layer
  (`unikernel/kernel.zig`, `unikernel/main.zig`, about 500 lines), Zig's musl
  1.2.5, the Lean compiler, the C compiler, the Lean runtime with a copied
  archive whose `initialize_libuv` is replaced by an empty one, and Cloud
  Hypervisor 54.0. A guest operating system is not in it. These are tested by
  `unikernel/check.sh`: byte-for-byte comparison of the serial stream with the
  Linux process, probes of the stack guard, system-call register and vector
  preservation, missing XSAVE or `RDRAND`, random failure, and negative
  controls that remove vector restore or red-zone protection. The guard
  covers contiguous stack growth only; a frame that jumps the whole 2 MiB
  guard is outside it. The Linux comparison shares the runtime adaptation, so
  it cannot find a defect they share. The clock is a stand-in from the tick
  counter; nothing a program computes depends on it.
- **That a guest did what its record says.** A record is checked, not
  believed. An accepted record is a run of the program and its process lines
  are that run's; a guest that remakes its chain can hand over a record of
  another run. A record is signed by its guest's entity key, which says who
  handed it over and not that it is true; the signature is checked by Zig,
  outside the kernel. Across machines a name is a number in
  a packet, taken as sent: that it cannot be forged is a hypothesis.
- **That a channel name cannot be guessed.** A name is a kind of data, so a
  number no longer hands a channel over, but a name value is not a key: a
  process can have one it does not hold, spliced into its code or answered
  from outside. What is proved is that a process cannot use a name it does not
  hold, where holding is kept by the scheduler, and holds each name once. Nothing is proved about a particular program of processes:
  not that it finishes, and not that it never waits forever.
- **What an operation computes.** The arithmetic table is nine Lean
  definitions with test scenarios. No theorem is about it.
- **Failure inside an operation.** An operation is a total function from data
  to data. It cannot fail as `wrong`; arithmetic answers `[]` for input it does
  not expect.
- **Cost and time.** Every budgeted run charges an operation its table cost
  and each step of the machine's own whose time grows with data its `work` or
  `reach`, before the step (`runPriced`, `arithCost`, `homoiconic-q59.73`).
  That a run asks each charge within the fuel left is proved
  (`runPriced_eq_within`). That a unit of charge takes a bounded time is not
  a theorem: it is measured, at most about 160 ns on morphie for the worst
  program found for each step (`openspec/specs/bytecode-machine/spec.md`, "A
  charge bounds a step's time"). The lazy machine of a kept session is not
  bounded so (`homoiconic-q59.80`).
- **The fault state outside compiled code.** `machine_never_faults` is about
  runs that start from `load (compile t)`. `step` does fault on code no term
  compiles to (`fault_reachable_from_uncompiled`), so a machine value or state
  that arrives as bytes rather than from the compiler is not covered.
- **Speed.** About 34 million machine steps per second, with operations
  emulated in compiled Lean.
- **A request carries no mark.** The driver reads every function a turn
  ends in as a request, so a driven program cannot finish with a function as
  its result, and one that returns a function by mistake may be read as
  asking.
- **Reaching only what a program was handed (P12).** A payload is data, and a
  program can build any data. Nothing here stops a program from naming
  something it was not given.
- **Completeness of the driver, and unfinished runs.** `converse` is proved
  sound, not complete: that every run is reported for some budget is not
  proved. When a turn does not finish within its budget, nothing is claimed,
  including about the requests listed before it.
- **A budget for a whole run.** The step budget is per machine run: the first
  evaluation, each reading of a payload, and each running of the rest on an
  answer get it afresh.
- **What a reference means.** That a reference names one piece, for ever, is
  assumed. The theorems state it as a hypothesis on the stores they compare.
  How a reference is made and checked is outside the kernel.
- **The byte form.** The reader and writer are tested, not proved, by
  decision D7. That they round-trip, and that no two values share a byte form,
  is tested on examples. Tag 2 for numbers of 2^64 and above and tag 39 for
  names are this project's rules, and text is not normalised to NFC as dCBOR
  asks. The identikey-protocol fixtures have not been compared: they hold maps
  and byte strings, which `Data` lacks.
- **The hash and the byte form of a piece.** Blake3 is checked against the
  official vectors, not proved to be Blake3. That no two pieces share a hash
  is assumed (D5). The byte form of a piece and saving are tested.
- **The session.** `Surface.Keep.advance` is tested against `driveRun`, not
  proved equal to it. Each machine run inside it is a turn the store theorems
  cover.
- **A function's code on the wire.** A function's byte form holds the program
  its code was compiled from. The claims about function values hold for code
  that is, at every depth, a compilation; a function whose code is not has no
  byte form.
- **Kept state on disk.** Only a waiting program is saved; a turn that runs
  out of steps is not kept, and a whole machine state has no byte form. A
  function's code is stored inside its piece, so two functions with the same
  code store it twice. Saving walks a value as a tree, so a value held in two
  places is encoded twice before the store holds it once. Fetching a whole
  value re-walks it after each piece arrives. Files are not written
  atomically. The hash, written in Lean, is slow next to a native one and has
  not been measured (`homoiconic-q59.20`).
- **Writing back.** The lazy machine does not write fetched pieces back to the
  state or the store. Remembering them is the store's.
- **Partial arguments.** An operation fetches its whole argument before it
  runs.
- **Finer cuts.** Code, the stack and the frame list are held whole. Their
  values and environments can be references.
- **Garbage collection.** Nothing is deleted. Which pieces no kept root
  reaches is not computed.
- **Fetch steps.** There is no bound on the number of steps the lazy machine
  takes to fetch.
- **An executable driver over stored state.** The theorems cover each turn.
  The session that runs a turn is tested, not proved. `converse` and the `ask`
  command still run in memory and replay from the start.
- **Sharing in the check.** `StoreCheck.lean` cuts a state as a tree, so a
  value held in two places is stored twice. Storing by hash removes the
  duplicates: the interpreter-twice state after 40 steps, cut at every value,
  is 168,796 saves and 774 distinct pieces.
- **The log.** An entry's identifier is the Blake3 hash of the entry. That
  two different entries do not share a hash is assumed, not proved: it is the
  hypothesis of `sealed_same`, and nothing proves it of Blake3. It also needs
  the byte form to tell different data apart, which is tested, not proved. Reading a log
  and sealing its entries is tested, not proved. Nothing is signed, and an
  entry does not name the one before it. An entry does not say which request it
  answers. Nothing says a state is the same under another order of
  deliveries. That a state reached by two routes is saved under one root is
  tested, not proved, and so is the session that handles a log against a
  store. The interpreter on data is not covered for a log.
- **Nodes.** The session that applies a log to kept processes is tested, not
  proved; `plan`, which it uses to decide what an event needs and gives, is
  proved to be `Step`. An op that cannot happen stops the log; nothing says
  it should be skipped or tried again. A kept node is taken at its word for
  what each process holds and is waiting on.
- **The network.** What a payload means, several VMs and model calls
  are the roadmap in `docs/VISION.md`.

## Next

Programs can run side by side in one machine and talk over channels, under a
recorded schedule. A waiting program can be kept on disk, under references made by Blake3. A
program's state is the fold of a handler over a log, a repeated entry changes
nothing, and a kept state handed its whole log reaches the state the log gives
from the start (vision stage 5: P13 and P14). One program
now runs in a Cloud Hypervisor image with no operating system; the image has
no network device yet (`add-unikernel-net`). Signatures, garbage collection and a store shared between machines are
not started.
