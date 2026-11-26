# Design: bound a kept session's time, space and stack

## Where the time goes on the lazy machine

`lstep` (`kernel/Reflect/Store.lean`) does work that grows with data in four places; every other lazy step is a constant amount of work (a fetch is one hash-map lookup):

| step | work | charged before |
|---|---|---|
| operation on a whole argument `x` (`lPrim`, `x.toData` is `some d`) | `x.toData` (a walk of `x` as a tree), `Ops.op n d`, the answer's `toP` | `Ops.cost n d`, found after a full `x.toData` in `lstepCost` |
| operation whose argument holds a reference | `x.toData` (fails at the reference, after walking all the rest) and `x.hyd σ` (rebuilds all of `x`) | 1 |
| `literal d` | `d.toP`, a walk of `d` | 1 |
| `succ`, `case` of a number, `cons` onto a text | as on the plain machine | `Ops.work`, as on the plain machine |

The tree of a piece can be exponentially larger than the objects it is made of: `dbl [0] k` is `k` objects and `2^k` leaves. So each of the first three can take time without bound for a charge of one, and `lstepCost` itself walks the argument before anything is compared with the budget.

## The charge

`convUnit = 8` (to be fixed by measurement, below): the pieces a unit of budget pays for converting.

```lean
/-- Pieces of a partial value counted as a tree: a cons one and its two parts,
    a function one and its environment, every other piece one. A reference
    is one: it is not followed. -/
def P.nodes : P R → Nat
/-- The pieces `d.toP` makes: a number, a name or a text one, an array one and,
    for each item, one and the item. `(d.toP : P R).nodes = d.nodes`. -/
def Data.nodes : Data → Nat

def lstepCost : PState R → Nat
  | .running (.prim _) _ (x :: .nat n :: _) _ =>
      match x.toData with
      | some d => Ops.cost n d + x.nodes / convUnit
      | none => 1 + x.nodes / convUnit
  | (the same for `.name n`)
  | .running (.literal d _) _ _ _ => 1 + d.nodes / convUnit
  | (succ, dcase, cons onto a text: `Ops.work`, unchanged)
  | _ => 1
```

So an operation is charged the plain machine's charge and the conversion on top, and the two agree whenever the argument has fewer than `convUnit` pieces (a pair of numbers is five). A literal of fewer than `convUnit` pieces is charged one, as on the plain machine.

`lstepCostWithin s cap` is the charge found within `cap`: count the argument's pieces with `P.nodesWithin x (convUnit * (cap + 1))` (a loop over a list of work, no recursion, that stops past its bound); only when the count is within it convert `x` (the conversion is then no larger than the count), and ask the table `Ops.costWithin n d (cap - c)`. Proved `lstepCostWithin_eq : lstepCostWithin s cap = min (lstepCost s) (cap + 1)`. The work it does is at most a few times what `cap` pays for, as on the plain machine.

### Where the lazy charge differs from the plain one

On every step the plain machine takes, `stepCost` and the lazy steps that simulate it differ in four ways, three of them already there before this change:

1. A variable lookup `access i` is `i + 1` lazy steps (`seeking`) of one each; the plain machine charges `i / 32 + 1`.
2. A fetch, and a hydration of an operation's argument, are lazy steps the plain machine does not take.
3. An operation is charged `x.nodes / convUnit` more (new).
4. A literal is charged `d.nodes / convUnit` more (new).

So a budget enough for the plain machine may not be enough for the lazy one; the lazy one is never charged less for a step both take. The theorems (`lazy_simulates`, `lazy_complete`, `lazy_sound`, `lazy_turn_complete`, `lazy_turn_sound`, the `Wire` and `Keep` proofs) are about `lstep` and `lrun`, which do not change, and about which states a session can be in; none of them states a charge, so none changes.

## The cells

A ledger of cells made, as `add-space-budget` gave the plain machine, with its own table read off `lstep`:

| lazy step | cells |
|---|---|
| `access` (to `seeking`) | 1 |
| `seeking` | 2 |
| `closure`, `checkFun`, `checkData` | 2 |
| `checkNat`, `apply` | 3 |
| `literal d` | 1 + `d.nodes` |
| `succ` | 2 + `natCells (n + 1)` (2 for anything else) |
| `cons` | 4, or 4 + 2n onto a text of n characters |
| `dcase` | 8, and `natCells` of a number |
| operation on whole data `x` | 2 + 6 `x.nodes` before the step (`x` converted twice, once to find the charge and once by the step, three objects a piece each time), and 2 + `Data.cells` of the answer after it |
| operation whose argument holds a reference | 2 + 5 `x.nodes` (the failed conversion and the rebuilt argument) |
| `done` with a frame | 0; the end of the program 2 |
| halted, fault | 0 |

A fetch replaces a part of the state with a piece the session holds: it is charged what its instruction is charged, which covers the list cells it rebuilds.

Unlike the plain machine, most of an operation's cells are charged **before** the step: the conversion of the argument can be as large as the budget pays for (eight pieces a unit), and it would exist before a run could be refused for it. Only the answer is charged after, as on the plain machine.

```lean
structure LSpace (R : Type) where
  cells : Nat
  count : PState R → Nat

inductive LEnded (R : Type) where
  | at : PState R → LEnded R          -- halted, out of steps, or fault
  | paused : R → PState R → LEnded R  -- the next step needs this piece
  | full : PState R → LEnded R        -- the next step would make more cells than are left

/-- What is left after `a` more cells: of the credit, or of the limit after a
    count of what `s` holds, at most three quarters of it. -/
def afford (sp : LSpace R) (credit : Nat) (s : PState R) (a : Nat) : Option Nat

def lrunSpace (σ : Store R) (sp : LSpace R) : (fuel credit : Nat) → PState R → LEnded R × Nat × Nat
  -- fuel 0, halted, fault: `at`, with fuel and credit as they are
  -- otherwise, with k := lstepCostWithin s (fuel + 1):
  --   k > fuel + 1                → at s (out of steps), nothing spent
  --   afford credit s (lowed s) = none → full s
  --   lstep σ s = needs r         → paused r s, nothing spent
  --   lstep σ s = next s', not an operation → go on from s' with what afford left
  --   an operation: afford credit s (lowed s + lanswered s') = none → full s, else go on
```

It gives back the fuel and the credit left, which the session carries across a pause. A paused step is charged nothing and found again when the piece comes; the work of finding its charge again is bounded by the fuel, and a pause happens once for each piece the host supplies.

### Theorems (`kernel/Reflect/StoreSpace.lean`, restated in `kernel/StoreContract.lean` with `#print axioms`)

For every table, store, `sp` (so every count), fuel, credit and state:

- `lrunSpace_lrun`: the state a run ends at (`at`, `paused` or `full`) is `lrun σ k s = .at t` for some `k ≤ fuel`; a run that ends `paused r t` has `lstep σ t = .needs r`. So `lazy_sound`, `lazy_complete` and the pause theorems apply to what a session holds.
- `lmade σ k s`: the cells the first `k` lazy steps from `s` make, by `lcharge`. `lrunSpace_ledger`: for the state `t` a run ends at, reached in `k` steps, either `lmade σ k s ≤ credit`, or for some `j ≤ k` the state `lrun σ j s` was counted at no more than `sp.bar` and that count and the cells made from it to `t` are within `sp.cells`. With the credit left `c'` on top of what was made in each case.
- `lrunSpace_within`: a run whose steps never pass its credit is not stopped for space.

These are the plain machine's `runSpace_run`, `runSpace_ledger` and `runSpace_within`, for the end state. `trail_held` (every state on the way) is not restated: every state on the way is the end state of the same run with less fuel only up to the credit, and nothing uses it.

## The session

- `Session` gains `space : LSpace Ref`-like fields: `cells`, the host's `count`, `credit`, and `held`, the cells of the pieces it has been given (a piece's `Data.cells`-like count, by a loop). The count a run uses is `count ps + held`: pieces fetched from the store count toward what the session holds, whether or not the state still reaches them.
- Each machine run (where the budget is reset, `left := budget`) starts with `credit := cells`, as `runIn` starts the plain run; a run paused for a piece resumes with the fuel and credit it had. `give` takes a piece's cells from the credit (to zero when they are more), so the next step counts when the pieces have spent it.
- `Keep.start`, `answer`, `vmStart`, `vmFrom`, `nodeStart`, `nodeFrom` take a space, by default `Space.ledger`-like (`count` answers more than the limit): every Lean check runs on the ledger alone. `Surface/Host.lean` gives the exports `Reflect.defaultSpace` and the runtime's count (`reflect_live_cells` on the `PState`, which walks Lean objects and is not specific to `State`), cut at the bar. The `keep`, `vm` and `node` commands take no new argument.
- A run that ends `full`: `no result within <cells> cells of a turn`, beside `no result within <budget> steps of a turn` (`homoiconic-q59.75`, for a kept session).

### What a session walks besides steps

- `full` (a result, a payload, a kept state's identifiers and results) is `partial` and recursive. It becomes `fullWithin σ p n`: a loop over a list of work that builds the data and counts it as `Data.written` counts it, and refuses past `4 * cells`, as `runTurn` refuses a data answer. The proofs know nothing of `full` but its type and keep knowing nothing else; a refusal is the space line.
- Saving (`save`, `cut`) walks the piece as a tree and hashes each part: a waiting program that holds doubled data takes time exponential in what it holds, and its bytes are few (equal parts hash alike). Before saving, `P.nodesWithin` the piece within `4 * cells`; past it, the space line. Within it, `cut` runs as a walk (below), so its time is the nodes counted.
- `chase`, `parts` and the readers of a kept state walk through at most `Session.reach` references and the pieces the store gave: bounded by the bytes supplied.

## The walks (`homoiconic-q59.78`)

Each recursion below is replaced by a loop over a list of work on the heap, swapped in by `@[csimp]` with a proof that it is the definition (as `3e0635d`, `kernel/WalkContract.lean`), so no definition a theorem mentions changes:

| function | recursion | how |
|---|---|---|
| `Data.toP`, `Data.listToP` | per level and per item | builder walk (`reifyGo`'s shape) |
| `MValue.toP`, `envToP` | per value and per entry | builder walk |
| `P.toData` | per level and per item | builder walk with failure |
| `P.hyd` | per level and per item | builder walk with a missing reference |
| `Wire.pieceItem`, `Wire.itemPiece` | per level and per item | builder walks |
| `Wire.cut` | per level and per item | a walk in `Saver` that keeps `cut`'s order of stores |
| `Data.decEq` | per level and per item | `decidable_of_iff` over `Data.same` (a subsingleton) |
| `Keep.full` | per level and per item, `partial` | replaced by the bounded `fullWithin` (above) |
| `Keep.parts`, `openProcs`, `renderNodeProcs`, `dataEntries`, `dataOps` | per item | accumulator loops |
| `Chan.dataEvents`, `renderProcs` | per item | accumulator loops |
| `Request.driveRun`, `Channel.schedIn`, `Channel.autoRun` | per answer or event | accumulator loops, proved equal |
| `Cross.readChain`; `readLines` appending entries | per entry; quadratic | accumulator loop; entries consed and reversed once |

A function with too little in it to be worth a proof is bounded instead, with one stated limit and its own refusal; none is planned.

Left: `Crossing.mix` (a crossing guest reaches it; its theorems are another agent's), `Data.cellsOnto` (only on an operation's answer). `Surface.Read`'s `TT.toTerm` recursion, found by this change's probe (a literal log of 300000 items ends the process in it), gets a bead: the source reader is not one of this bead's paths.

## Checks and controls

Each new check is shown failing (or timing out) on the tree before, `3122521`:

- `KeepCheck.lean`: the lazy charge of `add x 1` on doubled data is refused within the budget at 40 doublings, at once; a literal's charge; the charges agree with `stepCost` on a small argument; a turn out of space under a ledger of a few thousand cells gives the space line; a result past `4 * cells` written gives it.
- `host/check.sh`: `keep start` of `deep.hom` and `build.hom` end in `no result within 4000000 cells of a turn` under a memory bound (control: 542 MiB and the step line); `keep start` of `equal (dbl [0] 40) (dbl [0] 40)` and of `add (dbl [0] 40) 1` end in the step line within seconds (control: no answer in 120 s); a result list of 200000 items and a nest of a million (control: segfault); a waiting program holding a list of a million is saved (control: segfault); a `vm` log of 200000 entries (control: segfault); the same for `node` ops.
- `LogCheck.lean`, `NodeCheck.lean`: a long log handled.
- `CostBench.lean` `lazy` cases: no lazy case over 160 ns a unit.

What must not move: every line of `host/check.sh`'s output and of the `.txt` files it writes for inputs that worked before, the stored roots among them (`diff` before and after). Charges move only where an argument or a literal has at least `convUnit` pieces.

## Choices this leaves to Duke

1. **The count on a kept session.** As asked: the runtime's count when the ledger is spent, as `run` has. A `vm` or `node` replays a log, and past its ledger whether a turn goes on then depends on the runtime, not on the log alone; the plain drivers' turns use the ledger alone (`runTurn`) for that reason. The other way is the ledger alone on a kept session, which refuses a kept turn after about two million lazy steps.
2. **`convUnit`.** Eight pieces a unit by measurement; larger moves fewer charges and lets more time through each unit.

## The advise read, answered

`reviews/2026-11-25-advise.md` (Opus, fresh context, send-back, eleven findings). The read came after the walks in `Reflect/Store.lean` had been written; none of its findings touch them. In its order:

1. **Order.** `lrunSpace` asks first a floor of the charge that allocates nothing (`lfloor`: the argument's or the literal's pieces over `convUnit`, counted within the fuel; `lfloor_le : lfloor s ≤ lstepCost s`), refuses for steps when the floor is past the fuel, then affords `lowed s` (computed from the count, no conversion), and only then asks `lstepCostWithin`, which converts. A step past both limits can end `full` where the order budget-then-space would end `at`; the spec says so. `CostBench` measures the lazy cases at 100000000 as well.
2. **`lPrim`'s order.** `lstepCost`, `lowed` and `lfloor` charge a function on top of an operation's argument one (it halts `wrong` and walks nothing). The answer's cells are charged only when the step ran the operation (`lopAt`: the argument is whole data, by a walk that allocates nothing), and as twice its cells (`P.cells`, a walk): the answer exists as data and as a piece during the step.
3. **Saving.** The guard stays, and its limit and cost are stated: a piece counted as a tree, a closure's environment included, at most `4 * cells` units; time at most that many pieces, each closure's piece costing its code's size besides. A waiting program's environment doubles with each definition, so a program of more than about 22 definitions is refused; such a program did not finish saving before (measured: below). A sharing-aware `cut` (by the runtime's identity, as the count is) is a bead of its own. A refusal to save has its own line, not the turn's: `the state is too large to keep within <cells> cells`.
4. **One measure.** Saving and reading use one count of units (`P.units`): a number or a name five and its written digits, a text seven and four a character, an empty list two, a pair five, a reference one, a function one and its environment. Saving admits `4 * cells`; reading a kept state admits `5 * cells`, since reading also crosses the references `cut` made, at most one for every 256 bytes stored. A VM's or node's `seen` is part of what is saved, so a VM that has acted on more than about 160000 entries (a 256-bit identifier is about 97 units) cannot be kept; stated as a lifetime limit.
5. **A pause keeps its count.** A run that pauses, or that is refused for steps after its space was afforded, gives back `c1 + lowed s`, the credit after the count; `LHeld` covers it.
6. **The count.** `keep` is the only session given the runtime's count (below), and its count walks the run's state with the session's phase in one walk (`reflect_live_cells` on the pair), plus `held`, the bytes of the pieces given (a piece's cells are no more than its bytes). The pieces' hash map is not walked by the runtime count (arrays are not descended), which is why `held` is added.
7. **Per piece.** Stated: each `give` restarts the walk the session was in (`full`, `openState`, `openNode`, an operation's hydration), so a turn's time is bounded by its budget and the walks' limits for each piece supplied. Hydrating an argument stored across many pieces is charged one for every `convUnit` pieces at each level, a new limit, stated.
8. **`seen`.** The VM and the node keep their `seen` beside a hash set of the identifiers (`Data.same` and a hash of `Wire.write`), so each entry is looked up once.
9. **The count on `vm` and `node`.** Taken: a `vm` or `node` session runs every turn with the ledger alone at `turnSpace`, as `runTurn` runs the plain VM's and node's turns, so a log replays to one state on every machine. `keep` (one turn of a program, the kept form of `run`) has `Reflect.defaultSpace` and the runtime's count, as `run` has. This is the reading of "the same limit a plain run has" for each: the plain equivalent of `vm` and `node` is the driver's turn.
10. **Deltas.** Written: `specs/bytecode-machine`, `specs/state-store`, `specs/zig-host`.
11. The underflow cannot happen (the count past the cap returns `cap + 1` before the subtraction; `primCostWithin_eq` is proved). `Data.nodesWithin` is the literal's. `P.nodes` and `Data.nodes` run as loops (`@[csimp]`). `fullWithin` counts each reference it crosses. The answer counted twice (2). `trail_held` is not restated because nothing uses it; `lrunSpace_ledger` holds for every fuel and credit, and a run with less fuel stops at each state on the way with the credit it had there, which is the reason the end-state theorem covers them. The ledger's limit on an operation's argument, about `(cells − count) / 6` pieces (500000 at the default with little held), is stated in the spec; `run` has no such limit because the plain machine does not convert.
