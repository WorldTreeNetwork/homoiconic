import Reflect.Store
import Reflect.Space

/-!
The lazy machine of a kept session, priced and with a space limit
(`bound-kept-sessions`, `homoiconic-q59.70`, `homoiconic-q59.80`).

`lrunSpace` is to `lrun` what `runSpace` is to `run`: it takes `lrun`'s steps,
charges each its `lstepCost`, found within the fuel left
(`lstepCostWithin`), and counts the cells each makes in a ledger. When the
ledger is spent it asks how many cells the state holds, and goes on with the
difference when that is at most three quarters of the limit. It stops at a
state for want of fuel, pauses at one whose next step needs a piece the store
lacks, or stops out of space before a step that would make more cells than it
has left.

Most of an operation's cells are charged before its step, unlike the plain
machine's: the conversion of its argument to data can be as large as the
budget pays for, and must not be made before the run can refuse it.

The theorems are in `StoreSpaceProof.lean`.
-/

namespace Reflect
variable {R : Type} [Ops]

/-- Cells the lazy step from `s` makes, known before it is taken: for every
    step but an operation all of them, for an operation all but its answer.
    Each is at least the objects `lstep` makes for that case: the state's
    lists and frames, the pieces around data, a literal made a piece, and an
    operation's argument converted to data twice (once for its charge and
    once by the step, three objects a piece: the array, its list cell and
    the option around it) or rebuilt with its references replaced. A fetch
    puts a piece the session holds in place of a reference: it is charged as
    its instruction is. -/
def lowed : PState R → Nat
  | .seeking .. => 2
  | .running (.access _ _) _ _ _ => 1
  | .running (.closure _ _) _ _ _ => 2
  | .running (.literal d _) _ _ _ => 1 + d.nodes
  | .running (.checkFun _) _ _ _ => 2
  | .running (.checkData _) _ _ _ => 2
  | .running (.checkNat _) _ _ _ => 3
  | .running (.apply _) _ _ _ => 3
  | .running (.succ _) _ (.nat n :: _) _ => 2 + natCells (n + 1)
  | .running (.succ _) _ (.name n :: _) _ => 2 + natCells (n + 1)
  | .running (.succ _) _ _ _ => 2
  | .running (.cons _) _ (.text cs :: _) _ => 4 + 2 * cs.length
  | .running (.cons _) _ _ _ => 4
  | .running (.dcase _ _ _ _ _) _ (.nat n :: _) _ => 8 + natCells n
  | .running (.dcase _ _ _ _ _) _ (.name n :: _) _ => 8 + natCells n
  | .running (.dcase _ _ _ _ _) _ _ _ => 8
  | .running (.prim _) _ (.closure _ _ :: _) _ => 2
  | .running (.prim _) _ (x :: .nat _ :: _) _ => 2 + 6 * x.nodes
  | .running (.prim _) _ (x :: .name _ :: _) _ => 2 + 6 * x.nodes
  | .running (.prim _) _ _ _ => 2
  | .running .done _ _ (_ :: _) => 0
  | .running .done _ _ [] => 2
  | .halted _ => 0
  | .fault => 0

/-- Whether a piece is whole data: no function and no reference in it, and
    the rest of every pair a list. `P.toData` gives `some` exactly then; this
    walk makes nothing. -/
def pisDataGo : List (P R × Bool) → Bool
  | [] => true
  | (.nat _, list) :: ps => !list && pisDataGo ps
  | (.name _, list) :: ps => !list && pisDataGo ps
  | (.text _, list) :: ps => !list && pisDataGo ps
  | (.nil, _) :: ps => pisDataGo ps
  | (.cons h t, _) :: ps => pisDataGo ((h, false) :: (t, true) :: ps)
  | (.closure _ _, _) :: _ => false
  | (.ref _, _) :: _ => false
termination_by ps => P.nodesList (ps.map Prod.fst)
decreasing_by all_goals simp only [List.map_cons, P.nodesList, P.nodes]; omega

/-- Whether the next step runs an operation on whole data, and so leaves an
    answer on top of the stack (not a hydrated argument, not a fetch). -/
def lopAt : PState R → Bool
  | .running (.prim _) _ (x :: .nat _ :: _) _ => pisDataGo [(x, false)]
  | .running (.prim _) _ (x :: .name _ :: _) _ => pisDataGo [(x, false)]
  | _ => false

/-- `acc` and the cells of the pieces in `work`, counted as `Data.cells`
    counts data: a number its `natCells`, a text one and its length, a pair
    or an empty list one, a function one and its environment, a reference one. -/
def pcellsGo : List (P R) → Nat → Nat
  | [], acc => acc
  | .nat n :: ps, acc => pcellsGo ps (acc + natCells n)
  | .name n :: ps, acc => pcellsGo ps (acc + natCells n)
  | .text t :: ps, acc => pcellsGo ps (acc + 1 + t.length)
  | .nil :: ps, acc => pcellsGo ps (acc + 1)
  | .cons h t :: ps, acc => pcellsGo (h :: t :: ps) (acc + 1)
  | .closure _ e :: ps, acc => pcellsGo (e :: ps) (acc + 1)
  | .ref _ :: ps, acc => pcellsGo ps (acc + 1)
termination_by ps => P.nodesList ps
decreasing_by all_goals simp only [P.nodesList, P.nodes]; omega

/-- Cells an operation's answer took, read from the state its step led to:
    two, and twice the answer's cells, which exist as data and as a piece
    while the step runs. -/
def lanswered : PState R → Nat
  | .running _ _ (p :: _) _ => 2 + 2 * pcellsGo [p] 0
  | _ => 2

/-- Cells the lazy step from `s` to `s'` makes. -/
def lcharge (s s' : PState R) : Nat := lowed s + if lopAt s then lanswered s' else 0

/-- Cells the first `n` lazy steps from `s` make, a step that needs a piece
    its `lowed` and nothing after it. -/
def lmade (σ : Store R) : Nat → PState R → Nat
  | 0, _ => 0
  | n + 1, s =>
      match lstep σ s with
      | .next s' => lcharge s s' + lmade σ n s'
      | .needs _ => lowed s

/-- A limit in cells, and how many cells a lazy state holds when the run asks.
    As for `Space`, the count is a parameter: a host gives the runtime's. -/
structure LSpace (R : Type) where
  cells : Nat
  count : PState R → Nat

/-- Three quarters of the limit, as `Space.bar`. -/
def LSpace.bar (sp : LSpace R) : Nat := sp.cells - sp.cells / 4

/-- No count: the ledger is all a run has. -/
def LSpace.ledger (cells : Nat) : LSpace R := ⟨cells, fun _ => cells + 1⟩

/-- How a lazy run ends. -/
inductive LEnded (R : Type) where
  /-- Halted, or out of steps, or at the fault state. -/
  | at : PState R → LEnded R
  /-- The next step needs this piece, which the store lacks. -/
  | paused : R → PState R → LEnded R
  /-- Out of space: the next step would make more cells than are left. -/
  | full : PState R → LEnded R

def LEnded.state : LEnded R → PState R
  | .at s => s
  | .paused _ s => s
  | .full s => s

/-- What is left after `a` more cells at `s`: of the credit when it covers
    them, else of the limit after a count of `s`, when that is at most
    `sp.bar` and leaves room for them. -/
def afford (sp : LSpace R) (credit : Nat) (s : PState R) (a : Nat) : Option Nat :=
  if a ≤ credit then some (credit - a)
  else if sp.count s ≤ sp.bar ∧ a ≤ sp.cells - sp.count s then some (sp.cells - sp.count s - a)
  else none

/-- The lazy machine priced and space-limited: where it ends, with the fuel
    and the credit left. In order, before each step: a floor of its charge
    that converts nothing (`lfloor`) is compared with the fuel; the cells
    known before the step (`lowed`) are afforded; the charge itself
    (`lstepCostWithin`, which converts an operation's argument) is compared
    with the fuel, a charge of zero using one; the step is taken, and an
    operation's answer afforded too. So nothing is converted before the run
    could refuse it for space, and a step past both its fuel and its space can
    end `full`. A step that needs a piece pauses the run, with nothing spent;
    the credit it gives back, as when the charge is past the fuel after the
    cells were afforded, is what a count there left. -/
def lrunSpace (σ : Store R) (sp : LSpace R) : (fuel credit : Nat) → PState R → LEnded R × Nat × Nat
  | 0, credit, s => (.at s, 0, credit)
  | fuel + 1, credit, .halted o => (.at (.halted o), fuel + 1, credit)
  | fuel + 1, credit, .fault => (.at .fault, fuel + 1, credit)
  | fuel + 1, credit, s =>
          if lfloorWithin s (fuel + 1) ≤ fuel + 1 then
            match afford sp credit s (lowed s) with
            | none => (.full s, fuel + 1, credit)
            | some c1 =>
                if h : max 1 (lstepCostWithin s (fuel + 1)) ≤ fuel + 1 then
                  match lstep σ s with
                  | .needs r => (.paused r s, fuel + 1, c1 + lowed s)
                  | .next s' =>
                      if lopAt s then
                        match afford sp credit s (lowed s + lanswered s') with
                        | none => (.full s, fuel + 1, credit)
                        | some c2 =>
                            lrunSpace σ sp (fuel + 1 - max 1 (lstepCostWithin s (fuel + 1))) c2 s'
                      else lrunSpace σ sp (fuel + 1 - max 1 (lstepCostWithin s (fuel + 1))) c1 s'
                else (.at s, fuel + 1, c1 + lowed s)
          else (.at s, fuel + 1, credit)
termination_by fuel => fuel
decreasing_by all_goals omega

end Reflect
