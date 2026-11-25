# bytecode-machine

## MODIFIED Requirements

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

## ADDED Requirements

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

So a run of the default budget, 100000000, takes at most about 16 s of wall time on morphie, whatever the program, on the plain machine. The lazy machine of a kept session is not bounded by this: it converts an operation's argument to data, and a literal to a piece, in time that grows with the data (`homoiconic-q59.80`).

#### Scenario: The worst comparison at the default budget

- GIVEN `equal (dbl [0] 40) (dbl [0] 40)` at the budget 100000000
- WHEN the image is given its byte form at levels 0 and 1 on morphie
- THEN each ends in `no result within 100000000 steps` in 12 s and 11 s

