# bytecode-machine

## ADDED Requirements

### Requirement: A run counts the cells it makes

The package SHALL define `charge s s'`, the cells the step from the state `s` to `s'` makes, read from the two states and from nothing else: one for `access`; two for `closure`, `literal`, `checkFun` and `checkData`; three for `checkNat` and for `apply`; two and the cells of the number made for `succ`; four for `cons` onto an array and four and two for each character for `cons` onto a text; eight for `dcase`, and for a number the cells of its predecessor; two and the cells of the answer for `prim`; two for any other step that ends in a halted state; nothing for the end of a block that goes back to a frame, and nothing for a step from a state that is not running. The cells of a number SHALL be `natCells`: one below 2^63, else four and one more for each 64 bits. The cells of a data value SHALL be `Data.cells`, the value counted as a tree: a number or a name its `natCells`, a text one and one for each character, an array one and, for each item, one and the item. `madeIn n s` SHALL be the sum of `charge` over the first `n` steps from `s`. `charge` SHALL NOT be claimed to be the bytes a step allocates: that each charge is at least the objects `step` makes is checked by reading, not proved.

#### Scenario: A tail loop makes cells it does not keep

- GIVEN `examples/forever.hom` and `Space.ledger 4000000`
- WHEN `runIn` runs it with the fuel 100000000
- THEN it ends as `full`: the loop makes more than 4000000 cells in 100000000 steps, though its state repeats (`forever_cycle`)

### Requirement: A run stops before a step that would pass its space

The package SHALL define `Space`, a number of cells and a function `count : State → Nat`, and `runSpace sp fuel credit s`, which ends as `Ended.reached t` or `Ended.full t`. `runSpace` SHALL take the steps `runPriced fuel` takes, in the same order, and SHALL end as `reached` exactly where `runPriced` ends when it is not stopped for space. Before a step from `s` it can pay for, with `a = charge s (step s)`: when `a ≤ credit` it SHALL go on with `credit - a`; otherwise, with `m = sp.count s`, when `m ≤ sp.bar` (`sp.cells - sp.cells / 4`, three quarters of the limit) and `a ≤ sp.cells - m` it SHALL go on with `sp.cells - m - a`, and in every other case it SHALL end as `full s` without taking the step. A step the fuel cannot pay for ends the run as `reached` before space is looked at. `runIn sp fuel s` SHALL be `runSpace sp fuel sp.cells s`. `Space.ledger cells` SHALL be the space whose count always answers more than the limit, so a run under it ends as `full` when its ledger is spent. `runPriced`, `step`, `run`, `stepCost` and every theorem about them SHALL be unchanged.

The package SHALL prove, for every table, every `Space`, every fuel, credit and state, with no `sorry` and no axiom of this package:

- `runSpace_run`: the state the run ends at is `run n s` for some `n ≤ fuel`;
- `runSpace_priced`: a run that ends as `reached t` has `t = runPriced fuel s`;
- `runSpace_full`: a run that ends as `full t` has `t = run k s` for a `k < fuel` with `credit < madeIn (k + 1) s`;
- `runSpace_within`: when `madeIn fuel s ≤ credit`, the run is `reached (runPriced fuel s)`, whatever the count;
- `trail_held`, with `trail_last`: `trail sp fuel credit s` lists the states the run is in, its last is the state the run ends at, and every `u` in it is `Held sp credit s u`: it is `run k s` with `madeIn k s ≤ credit`, or it is `run k (run j s)` with `sp.count (run j s) ≤ sp.bar` and `sp.count (run j s) + madeIn k (run j s) ≤ sp.cells`;
- `runSpace_ledger`: the state the run ends at is `Held`;
- `runIn_ledger`: under `Space.ledger cells` the state the run ends at is `run k s` with `madeIn k s ≤ cells`;
- `machine_never_faults_space` and `machine_exact_space`: a run of a compiled program is never at the fault state, and what it halts with is what the program evaluates to.

These SHALL be restated in `kernel/MachineContract.lean` with their axioms printed. They bound the cells a run makes. They SHALL NOT be read as a bound on the cells a state holds computed from the state: the state is a tree, a part held in two places is not marked as one, and counted as a tree the state of a program of 20 definitions is 20447239 cells while it holds 152 objects. That a state holds no more than it began with and what was made since, that the count a host supplies is the cells held, and that a cell is at most 24 bytes are not proved. A count a host supplies need not be a function of the state; the theorems hold for every function, and so for the one that gives the answers a run got.

#### Scenario: A recursion that waits ends out of space

- GIVEN `def deep x = [x, ...deep x]` applied to 0, and the default space
- WHEN `host/out/run` runs it with the budget 100000000
- THEN it prints `no result within 4000000 cells` with peak resident memory under 256 MiB, where the priced run alone took 849 MiB

#### Scenario: A tail loop still ends in the budget

- GIVEN `examples/forever.hom` and the default space
- WHEN `host/out/run` runs it with the budget 100000000 at levels 0, 1 and 2
- THEN each prints `no result within 100000000 steps`, as before

#### Scenario: Inside the ledger the count does not matter

- GIVEN `examples/factorial.hom` at levels 0 and 1
- WHEN each runs under `Space.ledger 4000000`, whose count refuses every state
- THEN each halts with the answer the priced run gives (`kernel/Surface/Check.lean`)

### Requirement: A turn is a run under its own space with no count

`Reflect.turnSpace` SHALL be 4000000, a constant of its own and not the default a host is given: what a turn may make is part of what a log or a record replays to, and it is not written in the record, so it SHALL change only with the record's form. `Reflect.runTurn budget s` SHALL be `runIn (Space.ledger turnSpace) budget s`, with a run that ends as `full t` giving `t`, a run that halts with data `d` for which `Data.writes d (4 * turnSpace)` is false giving `s`, and every other run giving the state it reached. The package SHALL prove `runTurn_reach`: `runTurn budget s = t → ∃ n, run n s = t`. Every machine run a driver makes against a budget SHALL be `runTurn`: requests (`converse`, `driveRun`), channels and a guest of a crossing (`beginRun`, `turnRun`, `settleRun`, `stepRun`), the VM and the node (`bootRun` and the channel runs), the check of a crossing, and the answers, schedule and log programs those read. A turn out of space SHALL be reported as a turn out of steps is, with that text (`homoiconic-q59.75`). The statements of the driver theorems SHALL NOT change. The lazy machine of a kept session (`Surface.Keep.steps`) is not limited by this requirement (`homoiconic-q59.70`), and what a guest of a crossing holds between turns is not (`homoiconic-q59.71`).

#### Scenario: The driver contracts still pass

- GIVEN `RequestContract.lean`, `ChannelContract.lean`, `LogContract.lean`, `NodeContract.lean` and `CrossingContract.lean` as they were
- WHEN each is checked against the drivers that call `runTurn`
- THEN each passes with no line changed

## MODIFIED Requirements

### Requirement: Steps bound control depth
<!-- base: 7f05360526377abc510602bee2598e9fef8973de openspec/specs/bytecode-machine/spec.md -->

The package SHALL prove that the value stack plus the pending frames after `n` steps is at most that of the starting state plus `n`. This is all a step budget is proved to bound in memory. The environments, closures and data a state holds are not bounded by the step budget: a recursion whose calls wait on each other keeps a frame and its environment per pending call, as `depth_bound` allows, and a program that builds data keeps the data, so what such a run holds grows with its steps. What a run makes is bounded by a space limit, a second number beside the budget (`runSpace`, below). The vision's P3 (`docs/DECISIONS.md`), that after `n` steps a state holds at most `c * n` cells more than it began with, is not proved and is false as stated: one step of `cons` onto a text, or `succ` of a large number, makes cells without bound. What is proved in its place is that every state of a space-limited run was reached by steps that made no more cells than the run had left (`trail_held`, `runIn_ledger`). That bounds cells made. A bound on the cells a state holds, computed from the state, is not proved: counted as a tree a state is far larger than what it holds, and counted by distinct parts it is smaller unless equal parts are made one object (`homoiconic-q59.67`, `homoiconic-q59.74`).

#### Scenario: A budget bounds the stacks

- GIVEN a step budget
- WHEN any program is run within it
- THEN the stack and frame depth is within the stated bound
