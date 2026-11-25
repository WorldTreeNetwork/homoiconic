import Reflect.RunUntil

/-!
A space limit beside the step budget (`add-space-budget`, `homoiconic-q59.67`).

A run counts the cells it makes in a ledger. `runSpace` takes the steps
`runPriced` takes and stops before a step that would make more cells than it
has left. When the ledger is spent it asks how many cells its state holds and
goes on with the difference, if that is at most three quarters of the limit.

The count is a parameter, as the operation table is. The machine's state is a
tree: that two parts of it are one object in memory is not in it, so nothing
defined here can say what a state holds (counted as a tree, the state of a
program of 20 definitions is 20 million cells while it holds 152 objects). A
host supplies the count from its runtime. `Space.ledger` supplies none, and a
run under it has its ledger alone.

The theorems are in `SpaceProof.lean`. They bound the cells a run makes.
-/

namespace Reflect

/-- Cells of a number: one when it fits a machine word, else four and one
    more for each 64 bits. -/
def natCells (n : Nat) : Nat := if n < 9223372036854775808 then 1 else 4 + Nat.log2 n / 64

mutual
  /-- `acc` and the cells of a data value counted as a tree: a number or a
      name its `natCells`, a text one and one for each character, an array
      one and, for each item, one and the item. An array's items are walked by
      a tail call; an item that is an array is one call deeper. -/
  def Data.cellsOnto : Data → Nat → Nat
    | .nat n, acc => acc + natCells n
    | .name n, acc => acc + natCells n
    | .text cs, acc => acc + 1 + cs.length
    | .arr xs, acc => cellsItems xs (acc + 1)
  def cellsItems : List Data → Nat → Nat
    | [], acc => acc
    | x :: xs, acc => cellsItems xs (x.cellsOnto (acc + 1))
end

/-- Cells of a data value counted as a tree. Called on the answer of an
    operation, which for `arith` is nested at most once. -/
def Data.cells (d : Data) : Nat := d.cellsOnto 0

/-- An upper bound on the digits of a number and the mark of a name. -/
def natWritten (n : Nat) : Nat := Nat.log2 n / 3 + 2

mutual
  /-- `acc` and an upper bound on the bytes of a data value written as text:
      a number or a name a third of its bits and two, a text two and four for
      each character, an array two and, for each item, two and the item. -/
  def Data.writtenOnto : Data → Nat → Nat
    | .nat n, acc => acc + natWritten n
    | .name n, acc => acc + natWritten n
    | .text cs, acc => acc + 2 + 4 * cs.length
    | .arr xs, acc => writtenItems xs (acc + 2)
  def writtenItems : List Data → Nat → Nat
    | [], acc => acc
    | x :: xs, acc => writtenItems xs (x.writtenOnto (acc + 2))
end

/-- An upper bound on the bytes of a data value written as text. Its CBOR form
    is no longer, but for the headers of long texts and arrays (at most seven
    bytes each) and the tag of a name (two). This is the definition; `writes`
    is what runs. -/
def Data.written (d : Data) : Nat := d.writtenOnto 0

/-- What is left of `left` after the items of `cur` and then of each list of
    `work` are written, each item two and its `written`; `none` when they
    take more. Lists still to walk wait in `work`, so nothing here recurses on
    how deep the data is nested, and no more is looked at than `left` pays
    for. -/
def writesGo : (left : Nat) → (work : List (List Data)) → (cur : List Data) → Option Nat
  | left, [], [] => some left
  | left, w :: work, [] => writesGo left work w
  | left, work, .nat n :: xs =>
      if _h : 2 + natWritten n ≤ left then writesGo (left - (2 + natWritten n)) work xs else none
  | left, work, .name n :: xs =>
      if _h : 2 + natWritten n ≤ left then writesGo (left - (2 + natWritten n)) work xs else none
  | left, work, .text cs :: xs =>
      if _h : 4 + 4 * cs.length ≤ left then writesGo (left - (4 + 4 * cs.length)) work xs else none
  | left, work, .arr ys :: xs =>
      if _h : 4 ≤ left then writesGo (left - 4) (xs :: work) ys else none
termination_by left work => (left, work.length)
decreasing_by
  all_goals simp_wf
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)
  all_goals (apply Prod.Lex.left; omega)

/-- Whether `d` written takes at most `n` bytes, by `written` (and two, as an
    item is counted). -/
def Data.writes (d : Data) (n : Nat) : Bool := (writesGo n [] [d]).isSome

variable [Ops]

/-- Whether the next step runs an operation: the one step whose cells cannot
    be told before it is taken. -/
def atPrim : State → Bool
  | .running (.prim _) _ _ _ => true
  | _ => false

/-- Cells the step from `s` makes, for every step but an operation, by the
    instruction `s` is at. Each is at least the objects `step` makes for that
    case: the frame and its list cell, the environment cells, the boxes around
    data. A state that is not running is charged nothing, and neither is the
    end of a block that goes back to a frame. -/
def owed : State → Nat
  | .running (.access _ _) _ _ _ => 1
  | .running (.closure _ _) _ _ _ => 2
  | .running (.literal _ _) _ _ _ => 2
  | .running (.checkFun _) _ _ _ => 2
  | .running (.checkData _) _ _ _ => 2
  | .running (.checkNat _) _ _ _ => 2
  | .running (.apply _) _ _ _ => 3
  | .running (.succ _) _ (.data (.nat n) :: _) _ => 2 + natCells (n + 1)
  | .running (.succ _) _ (.data (.name n) :: _) _ => 2 + natCells (n + 1)
  | .running (.succ _) _ _ _ => 2
  | .running (.cons _) _ (.data (.text cs) :: _) _ => 4 + 2 * cs.length
  | .running (.cons _) _ _ _ => 4
  | .running (.dcase _ _ _ _ _) _ (.data (.nat n) :: _) _ => 8 + natCells n
  | .running (.dcase _ _ _ _ _) _ (.data (.name n) :: _) _ => 8 + natCells n
  | .running (.dcase _ _ _ _ _) _ _ _ => 8
  | .running (.prim _) _ _ _ => 2
  | .running .done _ _ (_ :: _) => 0
  | .running .done _ _ [] => 2
  | .halted _ => 0
  | .fault => 0

/-- Cells an operation's step made, read from the state it led to: two and
    the cells of the answer on top of the stack. -/
def answered : State → Nat
  | .running _ _ (.data d :: _) _ => 2 + d.cells
  | _ => 2

/-- Cells the step from `s` to `s'` makes: `owed s`, or for an operation
    `answered s'`. Only an operation's charge reads `s'`. That the charge
    covers what a step allocates is checked by reading `step`, not proved. -/
def charge (s s' : State) : Nat := if atPrim s then answered s' else owed s

/-- Cells the first `n` steps from `s` make. -/
def madeIn : Nat → State → Nat
  | 0, _ => 0
  | n + 1, s => charge s (step s) + madeIn n (step s)

/-- What a run may use: the cells it may make, and how many cells a state
    holds, asked when those are spent. The kernel does not say how cells are
    counted; a host's count need not even be a function of the state, and the
    theorems hold for every function. -/
structure Space where
  cells : Nat
  count : State → Nat

/-- The most a state may be counted at for its run to go on: three quarters
    of the limit. A run that is counted at more is out of space, so after a
    count a run has at least a quarter of its limit to make before the next,
    and counting costs at most three cells looked at for each cell made. -/
def Space.bar (sp : Space) : Nat := sp.cells - sp.cells / 4

/-- No count: every state is counted as more than the limit, so a run under
    this stops when its ledger is spent, and its outcome depends on nothing
    outside the kernel. -/
def Space.ledger (cells : Nat) : Space := ⟨cells, fun _ => cells + 1⟩

/-- How a space-limited run ends. -/
inductive Ended where
  /-- Halted, or out of steps (a running state), or at the fault state, which
      a compiled program never is. -/
  | reached : State → Ended
  /-- Out of space: the next step would make more cells than are left. The
      step was not taken. -/
  | full : State → Ended

/-- The state a run ended at. -/
def Ended.state : Ended → State
  | .reached s => s
  | .full s => s

/-- `runPriced`, with a ledger of cells: `credit` is what the run may still
    make. A step the fuel cannot pay for ends the run as `runPriced` ends,
    before space is looked at. Before a step it can pay for, the run charges
    the cells the step makes. When the credit covers them it goes on. When it
    does not, it asks how many cells the state holds: at most `sp.bar`, three
    quarters of the limit, and the step's cells within what is left of the
    limit, and it goes on with the rest; otherwise it ends as `full`, at the
    state it is in. -/
def runSpace (sp : Space) : (fuel credit : Nat) → State → Ended
  | 0, _, s => .reached s
  | _ + 1, _, .halted o => .reached (.halted o)
  | _ + 1, _, .fault => .reached .fault
  | fuel + 1, credit, .running c e stk frs =>
      if stepCost (.running c e stk frs) - 1 ≤ fuel then
        if atPrim (.running c e stk frs) then
          -- An operation: its cells are known once it has run.
          if answered (step (.running c e stk frs)) ≤ credit then
            runSpace sp (fuel - (stepCost (.running c e stk frs) - 1))
              (credit - answered (step (.running c e stk frs)))
              (step (.running c e stk frs))
          else if sp.count (.running c e stk frs) ≤ sp.bar ∧
              answered (step (.running c e stk frs)) ≤
                sp.cells - sp.count (.running c e stk frs) then
            runSpace sp (fuel - (stepCost (.running c e stk frs) - 1))
              (sp.cells - sp.count (.running c e stk frs) -
                answered (step (.running c e stk frs)))
              (step (.running c e stk frs))
          else .full (.running c e stk frs)
        else
          -- Any other step: its cells are known before it is taken, so the
          -- state is not held while it is.
          if owed (.running c e stk frs) ≤ credit then
            runSpace sp (fuel - (stepCost (.running c e stk frs) - 1))
              (credit - owed (.running c e stk frs))
              (step (.running c e stk frs))
          else if sp.count (.running c e stk frs) ≤ sp.bar ∧
              owed (.running c e stk frs) ≤ sp.cells - sp.count (.running c e stk frs) then
            runSpace sp (fuel - (stepCost (.running c e stk frs) - 1))
              (sp.cells - sp.count (.running c e stk frs) - owed (.running c e stk frs))
              (step (.running c e stk frs))
          else .full (.running c e stk frs)
      else .reached (.running c e stk frs)
termination_by fuel => fuel
decreasing_by all_goals omega

/-- One step of a space-limited run from a running state, with the charge
    written once: the two shapes in the definition are for the compiler, which
    then need not hold the state while a step that is not an operation is
    taken. -/
theorem runSpace_running (sp : Space) (fuel credit : Nat) (c : Code) (e : MEnv)
    (stk : List MValue) (frs : List Frame) :
    runSpace sp (fuel + 1) credit (.running c e stk frs) =
      if stepCost (.running c e stk frs) - 1 ≤ fuel then
        if charge (.running c e stk frs) (step (.running c e stk frs)) ≤ credit then
          runSpace sp (fuel - (stepCost (.running c e stk frs) - 1))
            (credit - charge (.running c e stk frs) (step (.running c e stk frs)))
            (step (.running c e stk frs))
        else if sp.count (.running c e stk frs) ≤ sp.bar ∧
            charge (.running c e stk frs) (step (.running c e stk frs)) ≤
              sp.cells - sp.count (.running c e stk frs) then
          runSpace sp (fuel - (stepCost (.running c e stk frs) - 1))
            (sp.cells - sp.count (.running c e stk frs) -
              charge (.running c e stk frs) (step (.running c e stk frs)))
            (step (.running c e stk frs))
        else .full (.running c e stk frs)
      else .reached (.running c e stk frs) := by
  rw [runSpace]
  by_cases h : atPrim (.running c e stk frs) = true <;> simp [charge, h]

/-- A run that begins with the whole limit to make. What its start state
    holds is not counted against it. -/
def runIn (sp : Space) (fuel : Nat) (s : State) : Ended := runSpace sp fuel sp.cells s

/-- The states a run is in, in order: `runSpace`'s recursion, keeping each
    state it passes. Nothing runs this; `trail_last` says its last state is
    where `runSpace` ends, and `trail_held` is stated of all of them. -/
def trail (sp : Space) : (fuel credit : Nat) → State → List State
  | 0, _, s => [s]
  | _ + 1, _, .halted o => [.halted o]
  | _ + 1, _, .fault => [.fault]
  | fuel + 1, credit, .running c e stk frs =>
      if stepCost (.running c e stk frs) - 1 ≤ fuel then
        if charge (.running c e stk frs) (step (.running c e stk frs)) ≤ credit then
          .running c e stk frs ::
            trail sp (fuel - (stepCost (.running c e stk frs) - 1))
              (credit - charge (.running c e stk frs) (step (.running c e stk frs)))
              (step (.running c e stk frs))
        else if sp.count (.running c e stk frs) ≤ sp.bar ∧
            charge (.running c e stk frs) (step (.running c e stk frs)) ≤
              sp.cells - sp.count (.running c e stk frs) then
          .running c e stk frs ::
            trail sp (fuel - (stepCost (.running c e stk frs) - 1))
              (sp.cells - sp.count (.running c e stk frs) -
                charge (.running c e stk frs) (step (.running c e stk frs)))
              (step (.running c e stk frs))
        else [.running c e stk frs]
      else [.running c e stk frs]
termination_by fuel => fuel
decreasing_by all_goals omega

/-- The space a host is given when it does not say: 96 MiB of state at 24
    bytes a cell, chosen by measurement for the 512 MiB image
    (`unikernel/README.md`). -/
def defaultSpace : Nat := 4000000

/-- The cells a turn may make: a machine run inside a driver. It is not
    `defaultSpace`. What a turn may make is part of what a log or a record
    replays to, and it is not written there, so this changes only with the
    record's form. -/
def turnSpace : Nat := 4000000

/-- The run a driver makes for one turn: under `turnSpace` with no count, so
    it is the same on every machine that replays it. A turn out of space is
    left at the state it stopped in, and a turn whose data answer would take
    more than four bytes written for each cell is left where it began; a
    driver sees a state that is not halted either way, and reports the turn
    as not finished. -/
def runTurn (budget : Nat) (s : State) : State :=
  match runIn (.ledger turnSpace) budget s with
  | .full t => t
  | .reached (.halted (.value (.data d))) =>
      if d.writes (4 * turnSpace) then .halted (.value (.data d)) else s
  | .reached t => t

end Reflect
