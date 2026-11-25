# Design: a space limit in the priced run

## What was measured, before choosing

Three candidates, each run beside `runPriced` on the same programs, compiled, on the Mac (2026-11-24, a throwaway harness, `kernel/SpaceBench.lean`, not kept). The harness charged a first table of cells a step; the table that landed (`charge`, below) charges a little more for checks and halts, and the figures that depend on it are measured again on what landed and recorded under "The default".

**A ledger that is never given back.** Each step charges the cells it makes; the run stops when the ledger is spent.

**The size of the state, every step.** The state counted as the tree it is: every environment, every value in it, every frame, by a walk of the whole state.

**A ledger, with the state counted when the ledger is spent.** The ledger as above; when it is spent, count the state once and go on with the difference.

| run (budget 100000000 unless it ends) | priced run | ledger alone, 8000000 cells | tree size every step | ledger, counted as a tree when spent | ledger, counted by the runtime when spent |
|---|---|---|---|---|---|
| factorial 30, level 0 (1165 steps) | answer | answer | answer | answer | answer |
| factorial 30, level 1 (55543 steps) | 28 M steps/s | answer | 4059 steps/s, tree 231365 | answer | answer |
| factorial 30, level 2 (4036172 steps) | 37 M steps/s | **out of space**: it makes over 8 million cells | 855 steps/s, tree past 6113811 | **out of space**: tree 6113811 | answer, 28 M steps/s, one count of 4605 cells |
| forever, level 0 | 47 M steps/s | **out of space** within 10 M steps (over a cell a step) | 12 M steps/s, tree 29 | budget | budget, 34 M steps/s, 16 counts of at most 30 cells |
| forever, level 1 | 37 M steps/s | **out of space** | 104275 steps/s, tree 15249 | budget | budget, 28 M steps/s, 25 counts of at most 1025 |
| forever, level 2 | 38 M steps/s | **out of space** | (not run) | budget, tree 1462403 | budget, 28 M steps/s, 25 counts of at most 3527 |
| 20 definitions and a tail loop, level 0 | 37 M steps/s | **out of space** | tree 20447239 | **out of space** at the first count | budget, 37 M steps/s, counts of 152 cells |
| `deep`, level 0 | 849 MiB on morphie, panic on the image | out of space | | out of space | out of space at 11 M steps, 231 MiB peak |
| `build`, level 0 (`def build acc = build [0, ...acc]`) | grows | out of space | | out of space | out of space at 83 M steps, 233 MiB peak |

Two results decide it.

1. **A ledger alone refuses what must run.** A tail loop makes more than a cell a step and drops it. Any limit small enough to protect 512 MiB (a cell is up to 24 bytes) is spent within ten million steps, so `forever.hom` at the default budget ends out of space and not in the budget reply, and factorial through two interpreters, 4 million steps, makes over 8 million cells and is refused. Both are existing checks. A ledger needs a way to take back what was dropped.

2. **No function of the state that leaves memory as it is can say what was dropped.** The machine's state is a value, a tree; that two parts of it are one object in memory is not in it. A closure holds the whole environment it was made in, and that environment holds the closures made before it, so each definition doubles the tree: 5 definitions are 631 cells as a tree, 10 are 19975, 20 are 20447239, and the program holds 152 objects. Through two interpreters `forever.hom` is 1.5 million cells as a tree and 3527 objects. A measure that counts each part where it is held refuses ordinary programs. A measure that counts each distinct part once is less than what is held, since two equal lists built separately are two objects, so it is unsound unless the run also makes equal parts one object when it counts (`homoiconic-q59.74`). This was not expected; it is in `docs/LEARNINGS.md`.

What is left is the third candidate with the count taken from the runtime, which is the only thing that knows what is shared.

## The choice

**A ledger of cells made, in the kernel and proved; a count of the cells held, by the runtime, asked only when the ledger is spent.**

- The ledger is pure. `charge s s'` is the cells the step from `s` to `s'` makes, read off the two states. Inside its ledger a run's outcome depends on the program, the budget and the limit alone.
- The count is a parameter. `runSpace` takes a `Space`: the limit in cells and a function `count : State → Nat`. Every theorem holds for every `count`, as every machine theorem holds for every operation table. The kernel library never says how cells are counted.
- The host supplies the count at the boundary (`kernel/Surface/Host.lean`): `reflect_live_cells` in `kernel/ffi.c` walks the state's objects by address and counts each once. It changes nothing and stops at a cut.
- A run that is not given a count has `Space.ledger n`, whose count always answers "too many". Its ledger is all it has, and its outcome is pure everywhere. Every `#eval`, every check in Lean, and every turn inside a driver uses it.

What this costs in the semantics, said plainly: past its ledger, whether a one-run export goes on or stops is decided by a number the runtime gives. That number is a property of objects, not of the value: two equal states can be shared differently. So the deployed run is `runSpace sp` for the function that gives the answers this run got, and the theorems, which hold for every function, hold of it; but "the same program and limits give the same outcome" is a fact about one build of the kernel, not a theorem. The same Lean objects on the image, on Linux and on the Mac make the same objects in the same order and give the same number; `check-net.sh` compares the guest's reply with the Linux process's for a run out of space. A different compiler could share differently and stop a run a few cells earlier or later. One more way the two can differ: the walk answers "too many" when it cannot get memory for its table, so a machine short of memory can refuse where a larger one goes on. `homoiconic-q59.74` removes the first: make the count the number of distinct parts and share the state when it is counted. Lean's runtime has such a pass (`ShareCommon`), which recurses on the native stack and so is not usable as it is on a long list.

### Options this leaves to Duke

1. **As built**: ledger and runtime count. Meets the acceptance cases. The ledger is a theorem; the count is trusted.
2. **Ledger alone** (`Space.ledger` on the exports too: one line in `Host.lean`). Pure everywhere, and the bound on cells made is the whole story. `forever.hom` at 100000000 steps and factorial through two interpreters end out of space, so three existing checks change sides; the default budget would have to come down to a few million steps, or the checks to change.
3. **A pure count** (`homoiconic-q59.74`): the run shares its state when it counts it. Pure everywhere and long runs go on, at the price of a hash-consing pass that is itself trusted to share.
4. **Take it out** (below).

## Definitions (`kernel/Reflect/Space.lean`)

```lean
/-- Cells of a number: one when it fits a machine word, else four and one
    more for each 64 bits. -/
def natCells (n : Nat) : Nat := if n < 2 ^ 63 then 1 else 4 + Nat.log2 n / 64

/-- Cells of a data value counted as a tree: a number or a name its
    `natCells`, a text one and one for each character, an array one and, for
    each item, one and the item. -/
def Data.cells : Data → Nat

/-- Cells the step from `s` to `s'` makes. Nothing for a state that is not running. -/
def charge (s s' : State) : Nat

/-- Cells the first `n` steps from `s` make. -/
def madeIn : Nat → State → Nat
  | 0, _ => 0
  | n + 1, s => charge s (step s) + madeIn n (step s)

/-- A limit in cells, and how many cells a state holds when the run asks. -/
structure Space where
  cells : Nat
  count : State → Nat

/-- No count: the ledger is all the run has. -/
def Space.ledger (cells : Nat) : Space := ⟨cells, fun _ => cells + 1⟩

inductive Ran where
  | reached : State → Ran   -- halted, or out of steps, or (never, for a program) fault
  | full : State → Ran      -- the next step would make more cells than are left

def Ran.state : Ran → State

def runSpace (sp : Space) : (fuel credit : Nat) → State → Ran
def runIn (sp : Space) (fuel : Nat) (s : State) : Ran := runSpace sp fuel sp.cells s

/-- The states a run is in, in order; the same recursion as `runSpace`. -/
def trail (sp : Space) : (fuel credit : Nat) → State → List State
```

`runSpace` is `runPriced` with one more test. With fuel left and a running state it reads `stepCost s`; a step the fuel cannot pay for ends the run at `s` as `reached s`, exactly as `runPriced` ends. Otherwise, with `s' = step s` and `a = charge s s'`:

- `a ≤ credit`: go on from `s'` with `credit - a`.
- else, with `m = sp.count s`: if `m ≤ sp.cells / 2` and `a ≤ sp.cells - m`, go on from `s'` with `sp.cells - m - a`; otherwise the run ends as `full s`. The step is not taken.

The step budget is tested first, so a run out of both is out of steps. A run starts with `sp.cells` of credit and no count: what the start state holds is on top of the limit, and is bounded by the limit on the program's bytes. Half the limit is the bar for going on so that a run cannot ask again and again: after a count the run has at least half the limit to make before the next, and a count looks at no more than half the limit of cells, so counting costs at most about one cell looked at for each cell made. It follows that a run that holds more than half its limit when it asks is refused: the limit is on cells made since a count, and half of it on cells held across one. The line says `within <cells> cells` for both.

`charge`, by the instruction `s` is at:

| step | cells |
|---|---|
| `access` | 1 |
| `closure`, `literal`, each of the three checks | 2 |
| `apply` | 3 |
| `succ` | 2 and `natCells` of the number made |
| `cons` onto an array | 4 |
| `cons` onto a text of `n` characters | 4 + 2n |
| `dcase` | 8, and for a number `natCells` of the predecessor |
| `prim` | 2 and `Data.cells` of the answer |
| a halt (the step ends in a halted state) | 2 |
| the end of a block with a frame to go back to; any step from a state that is not running | 0 |

Each is at least the objects Lean makes for that step in `step` (the frame and its list cell, the environment cells, the boxes around data), counted from the right-hand sides in `kernel/Reflect/Machine.lean`; the advise read counted them again and found `access`, `apply`, `cons` and the text case of `dcase` exact and the rest with room. A matched value that is built again (the three checks) is charged as new, though the compiled C reuses it when it is held once. Where a step makes fewer (a tail call pushes no frame) the charge is not lowered: charging too much costs only an earlier count.

`Data.cells` is defined by recursion on the value, once for each level of nesting. It is called on the answer of an operation only, and an answer of `arith` is nested at most once. The checks of a written answer (below) walk with a work list and do not recurse.

**Made before it is charged.** `step s` is computed before `charge` is tested, so the answer of `prim`, and the array `cons` makes of a text, exist for a moment before a run is refused for them. For `arith` that is at most the answer of `codes` on a text the run holds, two cells and a spare list cell for each character; it is in the memory sum below, not in the ledger.

**The written answer.** A value is written as the tree it is, so an answer of forty cells built by doubling is 2^40 as text or bytes, and a function's byte form writes each environment where it is held. Cells do not bound that, and they do not bound the printer either: measured on the Mac, `Surface.renderData` holds about 75 bytes for each item of an array of empty texts and 150 for each of 19 digits while it prints, so an answer of 3.5 million numbers, 7 million cells, took 531 MiB. So an answer has its own bound, in bytes written, checked before anything is written:

- `Data.written d` is an upper bound on the bytes of `d` as text and as CBOR: a number or a name a third of its bits and two, a text two and four for each character, an array two and, for each item, two and the item.
- `Data.writes d n` answers whether `Data.written d ≤ n`, looking at no more than `n + 1` bytes' worth, with a work list and no recursion on nesting.
- `Wire.fitsValue v n` is the same for a machine value's data form: data as above, a function as two, a hundred for each instruction of its code (its quoted body is about seven cells an instruction to build), the literals in it, and each captured value where it is held.
- An answer may take `4 * cells` bytes: 16 MB written for the default. `renderState` and `renderInterpreted` give the space line for a data answer that does not; `replyBytes` gives `[7]` for any answer that does not. At most 2.1 million items can be held under the default, so the printer's worst is about 2.1 million short items; the largest existing answer, 2097145 empty texts given as a literal, is 8388582 bytes written.

## Theorems (`kernel/Reflect/SpaceProof.lean`, restated in `kernel/MachineContract.lean` with `#print axioms`)

To be proved for every table, every `sp : Space` (so every count), every fuel, credit and state:

```lean
theorem runSpace_run : ∃ n, n ≤ fuel ∧ (runSpace sp fuel credit s).state = run n s

theorem runSpace_priced : runSpace sp fuel credit s = .reached t → t = runPriced fuel s

theorem runSpace_full : runSpace sp fuel credit s = .full t →
    ∃ k, k < fuel ∧ run k s = t ∧ credit < madeIn (k + 1) s

theorem runSpace_within : madeIn fuel s ≤ credit →
    runSpace sp fuel credit s = .reached (runPriced fuel s)

/-- What the ledger says of a state `u` of a run begun at `s` with `credit`. -/
def Held (sp : Space) (credit : Nat) (s u : State) : Prop :=
  (∃ k, run k s = u ∧ madeIn k s ≤ credit) ∨
  (∃ j k, run k (run j s) = u ∧ sp.count (run j s) ≤ sp.cells / 2 ∧
    sp.count (run j s) + madeIn k (run j s) ≤ sp.cells)

theorem trail_last : (trail sp fuel credit s).getLast? = some (runSpace sp fuel credit s).state

theorem trail_held : ∀ u ∈ trail sp fuel credit s, Held sp credit s u

theorem runSpace_ledger : Held sp credit s (runSpace sp fuel credit s).state

theorem runIn_ledger : ∃ k, run k s = (runIn (.ledger cells) fuel s).state ∧ madeIn k s ≤ cells

theorem machine_never_faults_space : (runSpace sp fuel credit (load (compile t))).state ≠ .fault

theorem machine_exact_space : (runSpace sp fuel credit (load (compile t))).state = .halted w →
    ∃ o, Direct [] t o ∧ w = MP.injO o
```

`trail_held` is the space bound: every state a run is in was reached from the start by steps that made no more than its credit, or from a state it passed through, counted at `m ≤ cells / 2`, by steps that made no more than `cells - m`. `trail` is a second function with `runSpace`'s recursion; `trail_last` ties the two. `runIn_ledger` is the bound with no count: the steps made at most `cells` cells. `runSpace_full` and `runSpace_within` are what is pure: no count can stop a run whose first `fuel` steps stay inside its credit, and such a run is the priced run. `madeIn` does not fall as `n` grows and a run takes at most `fuel` steps, which is why the hypothesis is at `fuel`.

`runPriced` and its theorems are untouched.

## What the theorems do not say

P3 reads "after `n` steps the state holds at most `c * n + size s₀` cells". What is proved differs from it twice.

- It is about cells **made**, a sum over steps, not cells **held**. That a state holds no more than it began with and what was made since is true of memory and is not a theorem, because holding is not a notion the state has (result 2 above).
- It is not linear in steps. One step of `cons` onto a text, or `succ` of a large number, makes cells without bound, so no constant `c` exists; the bound is the space limit, a second number beside the budget.

The chain from the theorem to bytes:

1. `charge` is at least the objects a step makes. Checked by reading `step` against the table, twice; not proved, since what `step` allocates is a fact about compiled Lean.
2. The count is at least the cells the state holds. `reflect_live_cells` counts every constructor object reachable from the state once, the program's code and the literals in it included, and a large number as its `natCells`. Trusted C; Lean's own evaluator cannot run it, so `host/check.sh` checks it through `host/out/run`. It is not a function of the state (above).
3. A cell is at most 24 bytes: a list cell, a closure and a frame are 24, a boxed value 16, a large number 24 and its digits. Lean's allocator rounds and keeps free pages; nothing here bounds that, and it is measured.
4. Not in the ledger at all:
   - the start state: the program's code and literals, bounded by the byte limit (2 MiB at boot, about 4.2 million cells at worst; 1176 bytes on the network);
   - an answer made before it is charged (above);
   - the walk's table and stack. The table is sized once for a count, the least power of two that is at least twice the cut and two, 8 bytes a slot: 32 MiB for the default. The stack grows by doubling to at most the cells counted, 16 MiB at the default;
   - the reader's and the compiler's working memory, by the byte limit;
   - the answer written: the printer's per-item memory and the bytes, by `4 * cells`;
   - the state object itself and a step's garbage, freed at once under reference counting.
5. A count happens when the ledger is spent, so between counts the bound is the ledger's.

The image's memory for all of this is not 512 MiB. `unikernel/kernel.zig` gives a quarter of what lies between the image and the stack to `brk` and the rest, about 360 MiB, to `mmap`, which is where Lean's allocator and the walk's table come from. The sum for `n` cells on the network guest is `24 n` bytes of state, up to `40 n` for a moment when the state is one text and `codes` is called on it, and `12 n` for the walk; at boot the start state, up to 100 MiB, is on top. That sum is over 360 MiB at 8000000 cells (the advise read measured 387 MiB on the Mac for a 2.5 million character text, its `codes` kept, and one `cons` onto it), which is why the default is not 8000000.

## The outcome and its bytes

- Text (`reflect_run`, `reflect_run_bytes`, `reflect_interp`): `no result within <cells> cells`, beside `no result within <budget> steps`.
- Reply (`reflect_reply_bytes`): `Wire.RunReply.space`, data `[7]`, bytes `81 07`. `readRunReply` reads it. Tags 0 to 6 and their bytes are unchanged; `kernel/WireReplyCheck.lean` holds the two mjolnir fixtures, factorial at 100000000 (`82008200c24e0d13f6370f96865df5dd54000000`) and forever at 5000 (`8101`), as checks.
- A turn inside a driver has no new line: out of space it is unfinished, as out of steps it is, and the driver's text still says `no result within <budget> steps of a turn`. That text is then wrong, and raising the budget will not help. Giving a turn out of space its own line touches every driver's result type, text and check, and is left to `homoiconic-q59.75`; the comments on `Stop.unfinished` and the drivers' `none` say both causes.

**A run that changes sides.** A reply changes only for a run that passes its space. One documented run does: the list of 209715 zeros written out, 1 MiB of program, through one interpreter, which `unikernel/README.md` records as answering at 317 MiB on the Linux process. It holds 3.7 million cells of program as data before it starts and is refused at its first count. It is not in a check. A run that needs 317 of the 360 MiB the image has is past any limit that protects the image; the README's row is corrected.

## Where the limit comes from

- `Reflect.defaultSpace`, in the kernel; a host asks for it with `reflect_default_space`, as it asks for `reflect_max_levels`.
- `reflect_run`, `reflect_run_bytes`, `reflect_interp` and `reflect_reply_bytes` take `space : u64` after `budget`. `Host.lean` makes the `Space` from it with the runtime's count, cut at half.
- `host/out/run … <program-file> [step-budget [space]]`; `unikernel/out/reply run <budget> <bytes> [space]`.
- The boot image: the command line is `[step-budget [levels [space]]]`.
- The network image: the word `reflect.space=<cells>`, default the kernel's. It applies to every run frame, over UDP and over QUIC. The `RFL1` frame keeps its 24 bytes: a sender does not choose the guest's memory, the guest's owner does.
- A guest with other memory is given another limit by whoever starts it, from the sum above against its own `mmap` area; the kernel does not read the machine's memory, and the sum is not proportional to it (the start state and the image are fixed costs).

## One ledger on every budgeted path

`Reflect.runTurn budget s` is the run every driver makes where it called `runPriced`: `runIn (.ledger turnSpace) budget s`, with a run out of space left at the state it stopped in and a data answer that does not fit (`Data.writes d (4 * turnSpace)`) left at `s`. Either way the driver sees a state that is not halted and reports the turn unfinished. Every state a driver starts a turn from is running, and no driver uses a state that is not halted, so nothing is misread. `runTurn_reach` (`runTurn budget s = t → ∃ n, run n s = t`) stands where `runPriced_reach` stood in the driver proofs, whose statements do not change: each has the form "if the driver reports finished or waiting, then".

`Reflect.turnSpace` is its own constant, 4000000, and is not the image's default: what a turn may make is part of what a log or a record replays to, as its budget is, and unlike the budget it is not written in the record. Changing it changes what old records replay to, so it is changed only with the record's form.

- Requests (`converse`, `driveRun`), channels and the guest of a crossing (`beginRun`, `turnRun`, `settleRun`, `stepRun`), the VM and the node, the answers, schedule and log programs, the check of a crossing: turns. No count, so a turn's outcome is the same on the guest that ran it and the machine that replays it.
- `reflect_run`, `reflect_run_bytes`, `reflect_interp`, `reflect_reply_bytes`: `runIn` with the runtime's count.
- **The lazy machine** (`Surface.Keep.steps` over `Reflect/Store.lean`): not limited. Its step is a second function with its own states; a piece fetched from the store is memory made too, and the pieces a state holds are not `State`'s cells. It needs its own charge table and proof. `homoiconic-q59.70`.
- **A guest of a crossing**: each turn is limited. What the guest holds across turns, every process's waiting state (each may be as large as a turn can make), the packets in and out and the log, is not, so a program that starts processes can still end a guest. `homoiconic-q59.71`.

## The default

`Reflect.defaultSpace = 4000000`: 96 MiB of state at 24 bytes a cell, 160 MiB for a moment at worst, 48 MiB for the walk, and at boot up to 100 MiB of program, against 360 MiB.

To be confirmed on morphie and recorded here and in `unikernel/README.md`, on the 512 MiB image started by `given.sh` and with the peak of the Linux process beside each: `deep` and `build` at levels 0, 1 and 2; a 2 million character text built, its `codes` kept and one `cons` onto it; an array of 2 million numbers of 19 digits answered, and of 2 million empty texts; a number squared until the budget stops it; an answer built by doubling; a function answered from a program of thirty definitions; and each of these behind a 2 MiB literal at boot. Each has to end in the kernel's text. If one does not, the default comes down until it does.

`deep` through two interpreters and `build` through one or two do not reach any such limit in 100000000 steps: they hold 270046, 101274 and 4974 cells when the budget ends them (the advise read's runs), and end in the budget reply. The checks give those a smaller space where that shows the limit working (`deep` at level 2 and `build` at level 1 with 100000), and say so.

## Taking it out

The change adds; it replaces little. To take it out: the exports call `runPriced` again and lose `space` (`Host.lean`, six Zig call sites); `runTurn` is defined as `runPriced` (one line; the driver proofs then go through `runPriced_reach` under the new name); `Reflect/Space.lean`, `Reflect/SpaceProof.lean`, `reflect_live_cells` and the contract lines are deleted; reply tag 7 stays reserved. `runPriced` and every theorem about it are as they were throughout.

## The advise read, answered

`reviews/2026-11-24-advise.md` (Fable, fresh context, send-back, fourteen findings). Each is answered above; in its order:

1. The printer runs out of memory on an answer that fits in cells: the answer has its own bound in bytes written, `4 * cells`, and the default's worst case is measured.
2. The memory sum for 8000000 cells does not hold: the sum is redone against the `mmap` area with the start state, the answer made before it is charged and the walk; the table is sized once; the default is 4000000.
3. The 1 MiB list through one interpreter changes sides: named and decided under "A run that changes sides".
4. `runSpace_within` was vacuous: its hypothesis is at `fuel`, and a state that is not running is charged nothing.
5. The new walkers could recurse on nesting: `Data.writes` and `Wire.fitsValue` use a work list; `Data.cells` is called on an operation's answer only.
6. The turn's limit must not move with the image's default: `turnSpace` is its own constant, and the proposal says a guest can still be ended.
7. The table's figures were the harness's charge: said, and measured again on what landed.
8. "Every state the run is in" was not a theorem: `trail`, `trail_last`, `trail_held`; `Ran.state` is in the definitions.
9. The runtime's count is not a function of the state: said under "The choice".
10. A failed allocation in the walk makes a reply depend on the allocator: said under "The choice"; the table is one allocation of a known size.
11. `natCells` and the walk disagreed by one for a large number: the walk counts the number's object as `natCells` less the box around it.
12. A turn out of space reads as out of steps: said, the comments corrected, `homoiconic-q59.75` for a line of its own.
13. The deltas: unobservable outcomes removed, the claim about replies narrowed to runs within their space, P3 stated as it is proved, the default one number.
14. Stated as done: the theorem list and the checks are written as to be done until they are.
