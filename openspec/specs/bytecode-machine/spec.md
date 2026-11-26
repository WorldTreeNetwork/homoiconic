# bytecode-machine

What is built: `Reflect.Machine`, a stack machine for the `Reflect` language. `compile` takes a term to continuation-form code, `step` is total on an explicit state, and `run n` takes `n` steps. `machine_correct`, `machine_exact`, `machine_never_halts`, `machine_never_faults`, `run_add`, `run_halted`, `runUntil_eq`, `runPriced_run`, `runPriced_reach`, `runPriced_unit`, `machine_exact_priced`, `decompile_compile`, `depth_bound`, `run_cycle`, `runPriced_cycle`, `omega_cycle`, `forever_cycle`, `forever_bounded`, and for a run with a space limit `runSpace_run`, `runSpace_priced`, `runSpace_full`, `runSpace_within`, `trail_last`, `trail_held`, `runSpace_ledger`, `runIn_ledger`, `machine_never_faults_space`, `machine_exact_space` and `runTurn_reach`, are proved and restated in `kernel/MachineContract.lean`. A block entered in tail position, a call or a case whose continuation is `done`, pushes no frame (`push`, `homoiconic-q59.65`), so a loop whose calls are in tail position runs in constant memory. `step`, `run`, and the theorems about them take the operation table `Ops` as a parameter and hold for every table. `runPriced` (`kernel/Reflect/RunUntil.lean`) runs the same steps against a budget that charges each operation the cost its table gives (`ab8e361`), and each step of the machine's own whose time grows with data what the table gives for that data (`charge-work-by-size`, `homoiconic-q59.73`); every budgeted path of the host runs it (`homoiconic-q59.52`), as `runPricedWithin`, proved equal, which finds each charge within the fuel left. `runSpace` (`kernel/Reflect/Space.lean`, `add-space-budget`) runs the same steps against a second number, a space limit in cells: it counts the cells each step makes, asks a count the host supplies how many the state holds when those are spent, and ends in an outcome of its own when the run would pass the limit. The speed measurement is in `docs/LEARNINGS.md`. The host runs `Reflect` programs on this machine through `reflect_run` (`openspec/specs/zig-host/spec.md`).

## Purpose

Name the machine that runs `Reflect` programs one step at a time, and its agreement with direct evaluation. This spec does not contain the language or the interpreter theorem (`openspec/specs/code-as-data/spec.md`), flattening to an array, serialized states, or a native executor.

## Requirements

### Requirement: Programs compile to code

The kernel package SHALL define an instruction set for the `Reflect` language and a total function `compile` from terms to code. The package SHALL prove that `decompile (compile t)` returns `t` for every term `t`.

#### Scenario: Code turns back into its term

- GIVEN any term
- WHEN it is compiled and then decompiled
- THEN the result is that term

### Requirement: The machine agrees with direct evaluation

The package SHALL define a machine state and a total function `step` on states. For every term `t` and outcome `o`, the package SHALL prove that `Direct [] t o` holds if and only if the machine, loaded with `compile t`, halts after some number of steps with an outcome that reads back as `o`. The package SHALL prove that whatever the machine halts with is exactly the compiled form of a source outcome, so that a returned closure holds the compiled code of its body. The package SHALL prove that a term with no derivation never halts. The package SHALL prove that the machine, loaded with `compile t` for any term `t`, is not in the fault state after any number of steps, under `run`, `runUntil` and `runPriced` alike; running out of budget leaves a running state, which is not the fault state. This is stated for compiled code only: `step` faults on code that no term compiles to.

#### Scenario: Identity

- GIVEN `app (lam (var 0)) (lam (var 0))`
- WHEN its code is run for seven steps
- THEN the machine has halted with the compiled identity closure

#### Scenario: Divergence

- GIVEN `omega`
- WHEN its code is run for any number of steps
- THEN the machine has not halted

#### Scenario: No fault without halting

- GIVEN `omega`, or any other term, closed or not
- WHEN its code is run for any number of steps, or under any priced budget
- THEN the machine is not in the fault state

### Requirement: A run can pause and continue

The package SHALL prove that running `n + m` steps from a state equals running `m` steps from the state reached after `n`. A halted state SHALL step to itself.

#### Scenario: Three slices

- GIVEN a program that halts after `n` steps
- WHEN it is run as three slices whose lengths sum to at least `n`
- THEN the outcome equals the outcome of one run

### Requirement: Steps bound control depth

The package SHALL prove that the value stack plus the pending frames after `n` steps is at most that of the starting state plus `n`. This is all a step budget is proved to bound in memory. The environments, closures and data a state holds are not bounded by the step budget: a recursion whose calls wait on each other keeps a frame and its environment per pending call, as `depth_bound` allows, and a program that builds data keeps the data, so what such a run holds grows with its steps. What a run makes is bounded by a space limit, a second number beside the budget (`runSpace`, below). The vision's P3 (`docs/DECISIONS.md`), that after `n` steps a state holds at most `c * n` cells more than it began with, is not proved and is false as stated: one step of `cons` onto a text, or `succ` of a large number, makes cells without bound. What is proved in its place is that every state of a space-limited run was reached by steps that made no more cells than the run had left (`trail_held`, `runIn_ledger`). That bounds cells made. A bound on the cells a state holds, computed from the state, is not proved: counted as a tree a state is far larger than what it holds, and counted by distinct parts it is smaller unless equal parts are made one object (`homoiconic-q59.67`, `homoiconic-q59.74`).

#### Scenario: A budget bounds the stacks

- GIVEN a step budget
- WHEN any program is run within it
- THEN the stack and frame depth is within the stated bound

### Requirement: A tail call keeps no frame

`step` SHALL push the frame `⟨k, env⟩` when it enters a function's body or a case branch whose continuation `k` is not `done`, and SHALL push nothing when `k` is `done` (`push` in `kernel/Reflect/Machine.lean`; `ppush` on the lazy machine). Such a frame would only end the block it returns to, and it held that block's environment. Dropping it SHALL change no outcome: `machine_correct`, `machine_exact`, `machine_never_faults` and the lazy machine's theorems SHALL hold with their statements unchanged. It SHALL change step counts: each dropped frame is one step `run` no longer takes (factorial 1290 steps to 1165 at level 0, 66758 to 55543 through one interpreter, 4816682 to 4036172 through two). The package SHALL prove that a run that comes back to a state it held stays within its first `a + p` states for any number of steps and any priced budget (`run_cycle`, `runPriced_cycle`), and SHALL prove by evaluation that `omega` and `examples/forever.hom` (`loopForever`) come back: `omega` from step 4 every 4 steps, forever from step 21 every 17, and forever through one interpreter, under `arith`, from step 853 every 832 (`forever_cycle_interp`), so a priced run of forever at any budget ends in one of 38 states, and through one interpreter in one of 1685 (`forever_bounded`). `kernel/Surface/Check.lean` SHALL check that forever's depth after 2000000 steps is at most 64 at levels 0, 1 and 2; with a frame per tail call it was 222222 at level 0.

#### Scenario: A tail loop at the default budget

- GIVEN `examples/forever.hom`
- WHEN `host/out/run` runs it with the budget 100000000 at levels 0, 1 and 2
- THEN each prints `no result within 100000000 steps` with peak resident memory under 64 MiB (`host/check.sh`; about 7 MiB at every budget, where a frame per tail call took 1153, 465 and 136 MiB)

#### Scenario: A recursion that waits still grows

- GIVEN `def deep x = [x, ...deep x]`, whose call waits on the next
- WHEN it runs with the budgets 1000000, 10000000 and 30000000
- THEN its peak memory grows with the budget (15, 91 and 260 MiB as a macOS process), within `depth_bound`

### Requirement: The machine runs operations

`compile` SHALL compile `prim c x` to the code of `c`, an instruction that checks the value on top is a number or a name, the code of `x`, and an instruction that replaces that value and the argument with the table's answer for its number. A value that fails the check SHALL halt the machine with `wrong` before the code of `x` runs. `step` and `run` SHALL take the table as a parameter. `machine_correct`, `machine_exact`, `machine_never_halts`, `run_add`, `run_halted`, `runUntil_eq`, and `depth_bound` SHALL hold for every table, with their statements unchanged by text and names. The instruction set SHALL be unchanged by text and names. An operation SHALL be one step.

#### Scenario: An operation on the machine

- GIVEN each operation scenario in `kernel/ReflectRun.lean`
- WHEN the compiled program runs on the machine, whole and in three slices
- THEN the halted outcome reads back as the outcome of direct evaluation

#### Scenario: Code with an operation turns back into its term

- GIVEN a term that contains `prim`
- WHEN it is compiled and decompiled
- THEN the result is the term

#### Scenario: Text and names on the machine

- GIVEN each text and name scenario in `kernel/ReflectRun.lean`
- WHEN the compiled program runs on the machine, whole and in three slices
- THEN the halted outcome reads back as the outcome of direct evaluation

### Requirement: The theorems depend on the logic only

`machine_correct`, `machine_exact`, `machine_never_halts`, `machine_never_faults`, `machine_never_faults_until`, `machine_never_faults_priced`, `run_add`, `run_halted`, `runUntil_eq`, `runPriced_run`, `runPriced_reach`, `runPriced_unit`, `machine_exact_priced`, `decompile_compile`, `depth_bound`, `run_cycle`, `runPriced_cycle`, `omega_cycle`, `forever_cycle`, `forever_cycle_interp`, `forever_bounded`, `runSpace_run`, `runSpace_priced`, `runSpace_full`, `runSpace_within`, `trail_last`, `trail_held`, `runSpace_ledger`, `runIn_ledger`, `machine_never_faults_space`, `machine_exact_space` and `runTurn_reach` SHALL be restated by a contract file. Their axiom dependencies SHALL NOT include `sorryAx` or an axiom declared by this package.

#### Scenario: No admitted correctness

- GIVEN the compiled theorem `machine_correct`
- WHEN its axiom dependencies are printed
- THEN `sorryAx` is absent and no axiom from this package is present

### Requirement: A budget charges an operation its cost before it runs

The table `Ops` SHALL hold `cost : Nat → Data → Nat` beside `op`, with one as its value when a table does not give it. It SHALL also hold `costWithin : Nat → Data → Nat → Nat` with the law `costWithin_eq : costWithin n d cap = min (cost n d) (cap + 1)`, `min (cost n d) (cap + 1)` when a table does not give it; `work : Data → Nat`; and `reach : Nat → Nat`, each one when a table does not give it (`charge-work-by-size`, 2026-11-25). `stepCost` SHALL be `cost n d` for a state whose next step runs operation `n` (a number, or a name whose number is `n`) on the data `d`; `reach (reachIn i env 0)` for a state at `access i` in the environment `env`, where `reachIn` is the places the lookup walks, `i` or the environment's length when that is less; `work (.nat n)` (or `work (.name n)`) for `succ` or `dcase` of a number or name `n`; `work (.text cs)` for `cons` onto the text `cs`; and one for every other state. `runPriced fuel s` SHALL take the same steps as `run`, in the same order, from the same states: the charge SHALL decide only whether the next step is taken, never which step it is. It SHALL stop, leaving the running state it is in, before a step whose charge is more than the fuel left; it SHALL take every step whose charge it can pay and subtract that charge, and a charge of zero SHALL use one unit, so every step uses at least one. A halted state SHALL stay halted. `step`, `run`, `runUntil` and the instruction set SHALL be unchanged, and an operation SHALL still be one step of `run`: what the charge counts is the budget, not the steps. What runs SHALL be `runPricedWithin` and `runSpaceWithin`, which ask `stepCostWithin s (fuel + 1)`, an operation's charge by `costWithin`, so that a step the fuel cannot pay for is found out in no more time than the fuel pays for; they SHALL be proved equal to `runPriced` and `runSpace` (`@[csimp]` `runPriced_eq_within`, `runSpace_eq_within`), so no definition or theorem about the runs changes. For the table `arith`, `arithCost` (`kernel/Reflect/Arith.lean`) SHALL charge addition, subtraction and `less` the sum of the operands' bit lengths, multiplication, division and remainder their product, `text` and `codes` one more than the length of the text or array, `equal` the smaller of its two values' weights, and every other operation or argument one; the bit length of a number `n` is `log2 n + 1`, so zero costs as one does. The weight of a value (`Data.weight`) SHALL be the value counted as a tree: a number or a name its 64-bit words (`log2 n / 64 + 1`), a text one more than its length, an array one more than the weights of its items; it bounds the pairs `Data.same` compares, which compares two arrays' lengths by walking both together (`lenEq`). `arithCostWithin` SHALL find `equal`'s charge by weighing both values within a bound that doubles from one up to the cap (`minWeightGo`), so it looks at no more of either value than a few times the smaller weight or the cap, and comparing a small value with a large one costs the small one. `arithWork` SHALL be a number's or a name's 64-bit words, a text's length and one, and one for anything else; `arithReach i` SHALL be `i / 32 + 1`. The charge SHALL be read from the argument without running the operation. A priced run SHALL stop at the state `run` reaches after some number of steps no more than the fuel (`runPriced_run`, and `runPriced_reach` for a state it stops at), so every theorem about what `run` reaches holds of what a priced run reaches; what a priced run of a compiled program halts with SHALL be what the program evaluates to (`machine_exact_priced`). With a table whose every charge, `cost`, `work` and `reach`, is one, `runPriced` SHALL equal `runUntil` (`runPriced_unit`, which takes the three as hypotheses since 2026-11-25). `machine_never_faults_priced` covers `runPriced` on compiled code for every table.

#### Scenario: A large product costs more than a small one

- GIVEN `arithCost` and the operation `mul`
- WHEN it is charged for `[2, 3]` and for two numbers of 40 nines
- THEN the charges are 4 and 17689, the product of 133 bits by 133 bits

#### Scenario: Comparing data built by doubling is charged what it weighs

- GIVEN `def dbl x n` that makes `[x, ...x]` `n` times, and `equal (dbl [0] 40) (dbl [0] 40)`
- WHEN `host/out/run` runs it with the budget 100000000 at levels 0 and 1, and the image is given its byte form
- THEN each prints `no result within 100000000 steps`, in 11 to 13 s on a Mac and on morphie (`host/check.sh`, `unikernel/check.sh`; over UDP the reply `81 01`, `check-net.sh`); charged one, one such comparison ran for hours (24 doublings took 1.78 s for one step on morphie, and each doubling doubles it)

#### Scenario: A light value against a heavy one

- GIVEN `equal 0 (dbl [0] 40)` and `equal (dbl [0] 10) (dbl [0] 10)`
- WHEN each runs with the budget 100000
- THEN they print `0` and `1`: the first is charged one, the second 2048 (`kernel/Surface/Check.lean`)

#### Scenario: Charges that moved

- GIVEN every program in `examples/` at levels 0, 1 and 2
- WHEN each runs to its end and its charges are summed, before and after 2026-11-25
- THEN only `calc.hom` (30 more) and `words.hom` (3 more) changed, at each level, from `equal` on texts; no check moved to the other side of its threshold, and the mjolnir fixture replies (factorial at 100000000, `82008200c24e0d13f6370f96865df5dd54000000`; forever at 5000, `8101`) are byte for byte what they were

#### Scenario: Out of budget is not a fault

- GIVEN any term and any fuel
- WHEN the compiled term is run with `runPriced`
- THEN the machine is not in the fault state (`machine_never_faults_priced`)

### Requirement: A charge bounds a step's time

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

Every machine run the host makes against a budget SHALL be charged as `runPriced` charges it, within a space (`runIn` for the one-run exports, `runTurn` for a driver's run; see "A run stops before a step that would pass its space"): the run command (`Surface.runText`, `Surface.runBytes`), the interpreter (`Surface.renderInterpreted`), the reply bytes (`Surface.replyBytes`), requests (`Reflect.converse`, `Reflect.driveRun`), channels and a guest of a crossing (`Reflect.beginRun`, `Reflect.turnRun`, `Reflect.settleRun`, `Reflect.stepRun`), the VM and the node (`Reflect.vmRun`, `Reflect.nodeRun`, through the channel runs), and the answers and schedule programs those read. A kept session runs on the lazy machine; its `steps` (`kernel/Surface/Keep.lean`) SHALL be `lrunSpace`, which charges `lstepCost` (`kernel/Reflect/Store.lean`), at least one, before each lazy step, found within the budget left ("A kept session's lazy run is priced and has a space"). A lazy step the budget left cannot pay for SHALL NOT be taken. The interpreter SHALL perform each operation of the program it runs as one machine primitive on the same operation number and argument (`interp`, the `prim` case), so a run of `interp` on a program pays the same charge for each operation as a direct run of the program, and at least one for each of the interpreter's own steps. The theorems about these drivers SHALL hold of the priced runs, through `runPriced_reach`.

#### Scenario: The interpreter pays at least what the program pays

- GIVEN `mul` applied to two numbers of 40 nines
- WHEN it is run directly and through one interpreter, each with the budget 18000
- THEN the direct run prints the product and the interpreted run prints `no result within 18000 steps`, and with the budget 200 both print `no result within 200 steps` (`host/check.sh`)

#### Scenario: A turn's budget charges an operation

- GIVEN `examples/ask.hom` and the log answering 20 and 22
- WHEN the VM runs it with the budget 50 and with 49
- THEN it gives a state at 50 and none at 49: `add 20 22` costs 10, where one step used to count one (`kernel/LogCheck.lean`)

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

`Reflect.turnSpace` SHALL be 4000000, a constant of its own and not the default a host is given: what a turn may make is part of what a log or a record replays to, and it is not written in the record, so it SHALL change only with the record's form. `Reflect.runTurn budget s` SHALL be `runIn (Space.ledger turnSpace) budget s`, with a run that ends as `full t` giving `t`, a run that halts with data `d` for which `Data.writes d (4 * turnSpace)` is false giving `s`, and every other run giving the state it reached. The package SHALL prove `runTurn_reach`: `runTurn budget s = t → ∃ n, run n s = t`. Every machine run a driver makes against a budget SHALL be `runTurn`: requests (`converse`, `driveRun`), channels and a guest of a crossing (`beginRun`, `turnRun`, `settleRun`, `stepRun`), the VM and the node (`bootRun` and the channel runs), the check of a crossing, and the answers, schedule and log programs those read. A turn out of space inside a driver SHALL be reported as a turn out of steps is, with that text (`homoiconic-q59.75`); a kept session's turn has its own line ("A kept session's lazy run is priced and has a space"). The statements of the driver theorems SHALL NOT change. A `vm` or `node` session SHALL run every machine run of its lazy machine under `LSpace.ledger turnSpace`, the ledger alone, as `runTurn` runs the plain VM's and node's turns, so a log replays to one state on every machine (`bound-kept-sessions`). A `keep` session, one turn of a program and the kept form of a run, has the default space and the runtime's count, as a run has ("The exports that make one run take a space", `openspec/specs/zig-host/spec.md`). What a guest of a crossing holds between turns is not limited by this requirement (`homoiconic-q59.71`).

#### Scenario: The driver contracts still pass

- GIVEN `RequestContract.lean`, `ChannelContract.lean`, `LogContract.lean`, `NodeContract.lean` and `CrossingContract.lean` as they were
- WHEN each is checked against the drivers that call `runTurn`
- THEN each passes with no line changed

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
