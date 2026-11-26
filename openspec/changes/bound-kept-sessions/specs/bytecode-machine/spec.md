# bytecode-machine

## MODIFIED Requirements

### Requirement: A charge bounds a step's time
<!-- base: a89e86aa0ef0fb6d6fd691b0cace8864e9b75c61 openspec/specs/bytecode-machine/spec.md -->

The charges SHALL be chosen so that the wall time of a priced run is bounded by its budget: for every operation of `arith` and every step of the machine's own, the worst program found SHALL take no more than 160 ns of wall time on morphie for each unit of budget it uses, where a plain step takes 30 to 40 ns. This is measured, not proved: `kernel/CostBench.lean` (`lake exe reflectCostBench <case> <size> <budget>`) runs each case below until its budget ends and prints the time for each unit of budget; it builds against the tree before 2026-11-25 as well. Measured on morphie (Linux x86_64, Lean 4.35.0 with GMP, 2026-11-25, other work running beside it, so within about a third); `unikernel/evidence/q59.73-measurements.log`:

| case | size | before, ns per unit | after, ns per unit |
|---|---|---|---|
| a tail loop (a plain step) | | 29 to 35 | 40 |
| `equal` of data doubled `k` times with itself | `k` = 20, 24, 40 | one step took 1.78 s at 24, twice that for each doubling; no answer in 120 s at 20 in a loop | 155 (paid, `k` = 20); 74 (refused, `k` = 40) |
| `equal` of 0 with data doubled 30 times | | 33 | 50 |
| `equal` of a text with itself | 1000000 characters | 42283 | 12.5 |
| `equal` of a number with itself | 1 MB | 1533 | 0.6 |
| `cons` onto a text | 1000000 characters | 956137 | 29 |
| `succ` (and `case`) of a number | 1 MB | 18783 | 2.1 |
| `case` of a number | 1 MB | 6550 | 1.0 |
| reaching a variable | 100000 deep | 20929 | 147 |
| `add`, `sub`, `less` of a number with itself | 1 MB | under 0.05 | under 0.05 |
| `mul` of a number with itself | 10 KB | under 0.01 | under 0.01 |
| `div`, `mod` by 3 | 1 MB | under 0.05 | under 0.05 |
| `codes` of a text; `text` of an array | 1000000 | 27; 24 | 28; 26 |

So a run of the default budget, 100000000, takes at most about 16 s of wall time on morphie, whatever the program, on the plain machine.

The lazy machine of a kept session SHALL be bounded the same way, by its own charge ("A kept session's lazy run is priced and has a space"): every case above and the lazy machine's own, run by `lrunSpace` on an empty store until its budget ends (`lake exe reflectCostBench lazy <case> <size> <budget>`), SHALL take no more than 160 ns of wall time on morphie for each unit of budget, at the budgets 100000 and 100000000 (`bound-kept-sessions`, `homoiconic-q59.80`). Measured on morphie (2026-11-26, tree `7d67ff2`, other work running beside it), ns per unit at the budgets 100000 and 100000000 (`openspec/changes/archive/2026-11-25-bound-kept-sessions/evidence/7d67ff2-lazybench.log`); on the tree before, at the budget 100000 on a Mac, `add` on data doubled 14, 16 and 18 times took 32600, 133000 and 538000 ns a unit, and a refused `equal` on data doubled 22 times 688 ms:

| case on the lazy machine | size | ns per unit, 100000 | ns per unit, 100000000 |
|---|---|---|---|
| a tail loop (a lazy step) | | 82 | 70 |
| `equal` of data doubled `k` times with itself | `k` = 20, 40 | 12; 14 | 106 (paid); 6 (refused) |
| `equal` of 0 with data doubled 30 times | | 9 | 6 (refused) |
| `add` of data doubled `k` times and 1 | `k` = 14, 18, 40 | 70; 7; 7 | 88; 95; 5 (refused) |
| a literal of `k` numbers, made each time round | `k` = 1000, 100000 | 88; 153 | 87; 108 |
| `equal` of a text with itself | 1000000 characters | 48 | 12 |
| `cons` onto a text | 1000000 characters | 76 | 62 |
| `succ`, `case` of a number | 1 MB | 10; 3 | 8; 1 |
| reaching a variable | 100000 deep | 127 | 68 |
| `codes` of a text; `text` of an array | 1000000 | 58; 66 | 74; 156 |
| `equal`, `add`, `sub`, `less`, `div`, `mod` of a number; `mul` | 1 MB; 10 KB | under 3 | under 1 |

So a kept turn of the default budget takes at most about 16 s of wall time on morphie for each piece the host supplies (`homoiconic-q59.88`).

#### Scenario: The worst comparison at the default budget

- GIVEN `equal (dbl [0] 40) (dbl [0] 40)` at the budget 100000000
- WHEN the image is given its byte form at levels 0 and 1 on morphie
- THEN each ends in `no result within 100000000 steps`, in 11 s and 12 s, and over UDP the reply `81 01` in 11.5 s (tree `73fefe9`, `unikernel/evidence/q59.73-73fefe9-check.log`, `-check-net.log`); the kernel before gave no answer in 120 s at either level and no reply over UDP (`unikernel/evidence/q59.73-controls.log`)

### Requirement: One budget means the same on every budgeted path
<!-- base: a89e86aa0ef0fb6d6fd691b0cace8864e9b75c61 openspec/specs/bytecode-machine/spec.md -->

Every machine run the host makes against a budget SHALL be charged as `runPriced` charges it, within a space (`runIn` for the one-run exports, `runTurn` for a driver's run; see "A run stops before a step that would pass its space"): the run command (`Surface.runText`, `Surface.runBytes`), the interpreter (`Surface.renderInterpreted`), the reply bytes (`Surface.replyBytes`), requests (`Reflect.converse`, `Reflect.driveRun`), channels and a guest of a crossing (`Reflect.beginRun`, `Reflect.turnRun`, `Reflect.settleRun`, `Reflect.stepRun`), the VM and the node (`Reflect.vmRun`, `Reflect.nodeRun`, through the channel runs), and the answers and schedule programs those read. A kept session runs on the lazy machine; its `steps` (`kernel/Surface/Keep.lean`) SHALL be `lrunSpace`, which charges `lstepCost` (`kernel/Reflect/Store.lean`), at least one, before each lazy step, found within the budget left ("A kept session's lazy run is priced and has a space"). A lazy step the budget left cannot pay for SHALL NOT be taken. The interpreter SHALL perform each operation of the program it runs as one machine primitive on the same operation number and argument (`interp`, the `prim` case), so a run of `interp` on a program pays the same charge for each operation as a direct run of the program, and at least one for each of the interpreter's own steps. The theorems about these drivers SHALL hold of the priced runs, through `runPriced_reach`.

#### Scenario: The interpreter pays at least what the program pays

- GIVEN `mul` applied to two numbers of 40 nines
- WHEN it is run directly and through one interpreter, each with the budget 18000
- THEN the direct run prints the product and the interpreted run prints `no result within 18000 steps`, and with the budget 200 both print `no result within 200 steps` (`host/check.sh`)

#### Scenario: A turn's budget charges an operation

- GIVEN `examples/ask.hom` and the log answering 20 and 22
- WHEN the VM runs it with the budget 50 and with 49
- THEN it gives a state at 50 and none at 49: `add 20 22` costs 10, where one step used to count one (`kernel/LogCheck.lean`)

### Requirement: A turn is a run under its own space with no count
<!-- base: a89e86aa0ef0fb6d6fd691b0cace8864e9b75c61 openspec/specs/bytecode-machine/spec.md -->

`Reflect.turnSpace` SHALL be 4000000, a constant of its own and not the default a host is given: what a turn may make is part of what a log or a record replays to, and it is not written in the record, so it SHALL change only with the record's form. `Reflect.runTurn budget s` SHALL be `runIn (Space.ledger turnSpace) budget s`, with a run that ends as `full t` giving `t`, a run that halts with data `d` for which `Data.writes d (4 * turnSpace)` is false giving `s`, and every other run giving the state it reached. The package SHALL prove `runTurn_reach`: `runTurn budget s = t → ∃ n, run n s = t`. Every machine run a driver makes against a budget SHALL be `runTurn`: requests (`converse`, `driveRun`), channels and a guest of a crossing (`beginRun`, `turnRun`, `settleRun`, `stepRun`), the VM and the node (`bootRun` and the channel runs), the check of a crossing, and the answers, schedule and log programs those read. A turn out of space inside a driver SHALL be reported as a turn out of steps is, with that text (`homoiconic-q59.75`); a kept session's turn has its own line ("A kept session's lazy run is priced and has a space"). The statements of the driver theorems SHALL NOT change. A `vm` or `node` session SHALL run every machine run of its lazy machine under `LSpace.ledger turnSpace`, the ledger alone, as `runTurn` runs the plain VM's and node's turns, so a log replays to one state on every machine (`bound-kept-sessions`). A `keep` session, one turn of a program and the kept form of a run, has the default space and the runtime's count, as a run has ("The exports that make one run take a space", `openspec/specs/zig-host/spec.md`). What a guest of a crossing holds between turns is not limited by this requirement (`homoiconic-q59.71`).

#### Scenario: The driver contracts still pass

- GIVEN `RequestContract.lean`, `ChannelContract.lean`, `LogContract.lean`, `NodeContract.lean` and `CrossingContract.lean` as they were
- WHEN each is checked against the drivers that call `runTurn`
- THEN each passes with no line changed

## ADDED Requirements

### Requirement: A kept session's lazy run is priced and has a space

The lazy machine's charge `lstepCost` (`kernel/Reflect/Store.lean`) SHALL count the conversions its step makes. An operation `n` on an argument `x` SHALL be charged `cost n d` when `x` is whole data `d` and one when it is not (the step hydrates it), and in both cases one for each piece of `x` past `convFree`, seven, where `P.nodes` counts `x`'s pieces as a tree (a pair one and its two parts, a function one and its environment, a reference one and not followed); a function as the argument SHALL be charged one (the step halts `wrong` and walks nothing). A literal `d` SHALL be charged one and one for each `convUnit`, eight, of its pieces (`Data.nodes`, the pieces `d.toP` makes). `succ` and `case` of a number and `cons` onto a text SHALL be charged `work`, as `stepCost` charges them; a variable lookup is a lazy step of one for each place passed; a fetch, and every other step, one. So the lazy charge SHALL be `stepCost` on an operation whose argument has at most seven pieces (a pair of numbers is five) and on a literal of fewer than eight, and never less for a step both machines take. `lstepCostWithin s cap` SHALL count an argument's or a literal's pieces within what `cap` pays for (`P.nodesWithin`, `Data.nodesWithin`, walks over a list of work that stop past their bound) and convert only what the count admits; `lstepCostWithin_eq : lstepCostWithin s cap = min (lstepCost s) (cap + 1)`. `lfloor s`, the conversion's part of the charge, SHALL be found from the count alone (`lfloor_le : lfloor s ≤ lstepCost s`, `lfloorWithin_eq`).

`lowed s` SHALL be the cells the lazy step from `s` makes that are known before it (for an operation all but its answer: two and six for each piece of its argument, which the step converts twice, three objects a piece each time; a literal one and its pieces; the rest of the table in `kernel/Reflect/StoreSpace.lean`, each at least what `charge` gives the plain step it simulates), and `lanswered s'` two and twice the cells of an operation's answer, which exists as data and as a piece while the step runs; `lcharge s s'` SHALL be `lowed s`, and `lanswered s'` when the step ran an operation on whole data (`lopAt`). `lmade σ k s` SHALL be the sum of `lcharge` over the first `k` lazy steps, a step that needs a piece its `lowed` and nothing after it. `LSpace` SHALL be a number of cells and a count of a lazy state; `LSpace.ledger cells` the space whose count answers more than the limit. `lrunSpace σ sp fuel credit s` SHALL end as `at t` (halted, out of steps, or the fault state), `paused r t` (the next step needs the piece `r`), or `full t` (the next step would make more cells than are left), with the fuel and the credit left. Before each step, in order: when `lfloorWithin s (fuel + 1)` is past the fuel it SHALL end `at s`; it SHALL afford `lowed s` from the credit, or from the limit after a count of `s` at no more than three quarters of it, and end `full s` when it cannot; when the charge `lstepCostWithin s (fuel + 1)` (at least one) is past the fuel it SHALL end `at s`; a step that needs a piece SHALL end `paused`, with nothing spent; an operation's answer SHALL be afforded after its step, and the run end `full s` when it cannot be. So nothing is converted before the run could refuse it for space, and a step past both its fuel and its space can end `full`. A run that pauses, or is refused for steps after its cells were afforded, SHALL give back the credit after the count.

The package SHALL prove, for every table, store, space (so every count), fuel, credit and state, with no `sorry` and no axiom of this package, and restate in `kernel/StoreContract.lean` with their axioms printed:

- `lrunSpace_ledger`: the state the run ends at is `lrun σ k s = .at t` for some `k ≤ fuel`; a run that ends `paused r t` has `lstep σ t = .needs r`; and the end is `LHeld`: the cells made on the way, with the credit left, are within the credit, or for some state on the way counted at no more than three quarters of the limit, that count and the cells made from it are within the limit;
- `lrunSpace_full`: a run that ends `full t` has `t = lrun σ k s` for a `k < fuel` with `credit < lmade σ (k + 1) s`;
- `lrunSpace_within`: when `lmade σ fuel s ≤ credit`, the run does not end `full`, whatever the count.

So `lazy_sound`, `lazy_complete` and the pause theorems apply to what a session holds. `trail_held` (every state on the way) is not restated: nothing uses it, and a run with less fuel stops at each state on the way. The theorems bound the cells the lazy machine's steps make; that each `lowed` and `lanswered` is at least the objects `lstep` makes is checked by reading, not proved. The ledger limits an operation's argument in a kept session to about `(cells − count) / 6` pieces, 500000 at the default with little held; `run` has no such limit because the plain machine does not convert.

A kept session (`kernel/Surface/Keep.lean`) SHALL run each machine run (where the budget is reset) with the credit its cells, and a run paused for a piece SHALL resume with the fuel and the credit it had; a piece given SHALL take its bytes from the credit, to zero. A `keep` session's count SHALL be the runtime's count of its phase and run state in one walk and the bytes of the pieces it was given (`held`), which the runtime's count does not reach. A turn that ends `full`, and a result or payload that written would take more than four bytes a cell (`fullWithin`, which refuses past `4 * cells` units), SHALL give `no result within <cells> cells of a turn`.

#### Scenario: A recursion that waits ends out of space in a kept turn

- GIVEN `def deep x = [x, ...deep x]` applied to 0, and `def build acc = build [0, ...acc]` applied to `[]`
- WHEN `host/out/keep` starts each with the default budget
- THEN each prints `no result within 4000000 cells of a turn` under 256 MiB (127 MiB and 115 MiB on a Mac), where the kernel before held 542 MiB for `deep` and printed the step line (`host/check.sh`)

#### Scenario: An operation on doubled data in a kept turn

- GIVEN `equal (dbl [0] 40) (dbl [0] 40)` and `add (dbl [0] 40) 1`
- WHEN `host/out/keep` starts each with the default budget
- THEN each prints `no result within 100000000 steps of a turn` in under a second under 64 MiB, where the kernel before ran until it failed, at 3.4 GiB after 115 s and 17 GiB after 50 s (`host/check.sh`)

#### Scenario: The lazy charge agrees with the plain one on small arguments

- GIVEN operation 3 on `[2, 3]` and on five numbers, and a literal of twenty numbers
- WHEN `lstepCost` and `stepCost` charge them
- THEN the first is charged the same by both, the second four more by the lazy machine, and the literal `1 + 41 / 8` (`kernel/KeepCheck.lean`)

#### Scenario: A kept turn out of its ledger

- GIVEN `deep 0` and the ledger of 2000 cells, and `fill 500 []` and the ledger of 100 cells
- WHEN `Keep.start` runs each with the budget 1000000
- THEN each gives `no result within <cells> cells of a turn`, and with the space undone the step line and the list (`kernel/KeepCheck.lean`)
