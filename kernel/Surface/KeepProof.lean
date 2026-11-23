import Surface.Keep
import Wire.PieceProof
import Reflect.LogProof

/-! Equal VM states are saved under one root.

    `Reflect.log_restart` says a state restarted on its whole log is the state
    a replay reaches. Here: the two are saved under the same root, however
    much of each a session holds as references, when every reference was made
    by saving (`Wire.Made`).

    What is assumed, as a hypothesis and not proved: that the piece a session
    holds at the end is `Made` for the state the log theorems speak of. `cut`
    makes only such references (`Wire.cut_made`) and the lazy machine makes
    none (`Wire.lstep_good`), but the session that joins the runs is not
    proved (`full` and `chase` are `partial`), and neither is that a piece read
    from its bytes is the piece that was written. Nothing is assumed of the
    hash. -/

namespace Surface.Keep
open Reflect Wire

/-- Where a program stands, as the whole piece a session saves for it. -/
def standing : Status MValue MOutcome → P Ref
  | .waiting c _ => .cons (.nat 0) (.cons c.toP .nil)
  | .finished (.value v) => .cons (.nat 1) (.cons v.toP .nil)
  | .finished (.unbound i) => .cons (.nat 2) (.cons (.nat i) .nil)
  | .finished .wrong => .cons (.nat 3) .nil

/-- A VM's state as a whole piece, with no reference in it. -/
def wholeState (w : MVm) : P Ref := vmState w.seen (standing w.status)

variable {size : Nat} {σ σ' : Store Ref}

/-- A session's state piece stands for the VM's state when its status piece
    stands for where the program stands. The identifiers are held whole. -/
theorem made_state {seen : List Data} {st : P Ref} {status : Status MValue MOutcome}
    (h : Made size σ st (standing status)) :
    Made size σ (vmState seen st) (wholeState ⟨status, seen⟩) :=
  .cons (Made.data _) (.cons h .nil)

/-- The status piece of a waiting program, the function held as `k`. -/
theorem made_waiting {k : P Ref} {c : MValue} {d : Data} (h : Made size σ k c.toP) :
    Made size σ (.cons (.nat 0) (.cons k .nil)) (standing (.waiting c d)) :=
  .cons .nat (.cons h .nil)

/-- The status piece of a data result. -/
theorem made_value (d : Data) :
    Made size σ (.cons (.nat 1) (.cons d.toP .nil)) (standing (.finished (.value (.data d)))) :=
  .cons .nat (.cons (Made.data d) .nil)

theorem made_unbound (i : Nat) :
    Made size σ (.cons (.nat 2) (.cons (.nat i) .nil)) (standing (.finished (.unbound i))) :=
  .cons .nat (.cons .nat .nil)

theorem made_wrong : Made size σ (.cons (.nat 3) .nil) (standing (.finished .wrong)) :=
  .cons .nat .nil

/-- One VM state has one root: two pieces that stand for it, every reference
    in each made by saving, are saved under the same root. -/
theorem state_same_root {w : MVm} {a b : P Ref} (ha : Made size σ a (wholeState w))
    (hb : Made size σ' b (wholeState w)) :
    (save size a).map (·.1) = (save size b).map (·.1) :=
  same_root ha hb

variable [Ops]

/-- A state kept after a first part of the log and restarted on the whole log
    is saved under the root a replay of the whole log from the start is saved
    under. `a` is what the restarted session holds at the end and `b` what the
    replaying one holds; the stores may differ. -/
theorem restart_same_root {p : Term} {l₁ l₂ : List Entry} {s v v' : Vm Value Outcome}
    (h : Logged sourceP p l₁ s) (hr : Replay source s (l₁ ++ l₂) v)
    (hl : Logged sourceP p (l₁ ++ l₂) v') {a b : P Ref}
    (ha : Made size σ a (wholeState (v.map MP.injO MP.injV)))
    (hb : Made size σ' b (wholeState (v'.map MP.injO MP.injV))) :
    (save size a).map (·.1) = (save size b).map (·.1) := by
  cases log_deterministic ((log_restart h).mp hr) hl
  exact same_root ha hb

end Surface.Keep
