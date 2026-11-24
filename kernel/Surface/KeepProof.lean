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
    none (`Wire.lstep_good`). For a session that runs one turn of a program
    the second half of this file proves that every reference it holds and
    saves was made by saving (`advance_turn`). `Surface/KeepLogProof.lean`
    proves the same of a VM and of a node (`advance_kept`), which is the half
    of `Made` that is about how the references were made. The other half,
    that the piece resolves to the state the log theorems speak of, is not
    proved of any session, and neither is that a piece read from its bytes is
    the piece that was written. Nothing is assumed of the hash. -/

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

section
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

end

/-! ## A turn of `keep` saves only references that saving made

    A session that runs one turn of a program (`start`, `answer`, `give`; not
    a VM, not a node) holds, in every phase, only references that `cut` made
    (`Inv`), and when it ends in a request the function it saves is such a
    piece (`Turn.waits`). So the root it reports is the root of the value held
    whole (`waits_root`), and the next turn, which starts from that root,
    starts with the invariant again (`Wire.save_opened`, `answer_turn`).

    `σ` is the whole store: every piece ever saved, each under its reference.
    The session holds a part of it. That the part stays a part when a piece is
    supplied is a hypothesis of `give_turn`. -/

/-- Every reference a phase of one turn holds was made by saving. The phases
    of a VM and of a node are covered by `PhaseHeld`
    (`Surface/KeepLogProof.lean`). -/
def PhaseGood (σ : Store Ref) : Phase → Prop
  | .run st => GoodS pieceSize σ st
  | .classify v => Good pieceSize σ v
  | .payload k st => Good pieceSize σ k ∧ GoodS pieceSize σ st
  | .ask k _ => Good pieceSize σ k
  | .result _ => True
  | .resuming r _ => ∃ p, σ r = some p ∧ Good pieceSize σ (opened pieceSize r p)
  | .done => True
  | _ => False

/-- A session of one turn: what it holds is part of `σ`, every reference in
    its phase was made by saving, and it has stored nothing yet. -/
structure Inv (σ : Store Ref) (s : Session) : Prop where
  le : s.store.le σ
  good : PhaseGood σ s.phase
  vm : s.vm = none
  node : s.node = none
  written : s.written = #[]

/-- Where a session of one turn can be after it was carried on. -/
inductive Turn (σ : Store Ref) : Session → Prop where
  /-- It goes on, or needs a piece, and still holds only such references. -/
  | holds {s : Session} : Inv σ s → Turn σ s
  /-- It ended in a request and saved the function `k`. -/
  | waits {s : Session} {d : Data} {k : P Ref} : Good pieceSize σ k → Turn σ (s.wait d k)
  /-- It is over and stored nothing. -/
  | over {s : Session} : s.phase = .done → s.written = #[] → Turn σ s

/-- Following references keeps a reference one that saving made. -/
theorem chase_good (hle : σ'.le σ) : ∀ (n : Nat) {v k x : P Ref}, Good size σ v →
    chase σ' n v = .ok (k, x) → Good size σ k
  | 0, v, k, x, hg, h => by
    cases v <;> simp only [chase, Except.ok.injEq, Prod.mk.injEq] at h <;> exact h.1 ▸ hg
  | n + 1, v, k, x, hg, h => by
    cases v with
    | ref r =>
      simp only [chase] at h
      cases hr : σ' r with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨p', hr', hp'⟩ := good_ref hg
        cases (hle _ _ hr).symm.trans hr'
        cases p with
        | ref r' =>
          simp only [hr] at h
          exact chase_good hle n hp' h
        | _ =>
          simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
          exact h.1 ▸ hg
    | _ => simp only [chase, Except.ok.injEq, Prod.mk.injEq] at h; exact h.1 ▸ hg

/-- A machine run of a session keeps every reference one that saving made,
    whether it ends at a state or pauses at one. -/
theorem steps_good (hle : σ'.le σ) : ∀ (n : Nat) {st : PState Ref} {out : LRun Ref} {left : Nat},
    GoodS size σ st → steps σ' n st = (out, left) →
    (∀ st', out = .at st' → GoodS size σ st') ∧ ∀ r st', out = .paused r st' → GoodS size σ st' := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro st out left hg h
    have stay : out = .at st →
        (∀ st', out = .at st' → GoodS size σ st') ∧ ∀ r st', out = .paused r st' → GoodS size σ st' :=
      fun e => e ▸ ⟨fun _ e => (by cases e; exact hg), fun _ _ e => (by cases e)⟩
    cases n with
    | zero =>
      unfold steps at h
      simp only [Prod.mk.injEq] at h
      exact stay h.1.symm
    | succ n =>
      unfold steps at h
      split at h
      · simp only [Prod.mk.injEq] at h; exact stay h.1.symm
      · simp only [Prod.mk.injEq] at h; exact stay h.1.symm
      · split at h
        · split at h
          · rename_i s' hl
            exact ih _ (by omega) (lstep_good hle hg hl) h
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact ⟨fun _ e => (by cases e), fun _ _ e => (by cases e; exact hg)⟩
        · simp only [Prod.mk.injEq] at h; exact stay h.1.symm

variable {s : Session}

theorem finish_over (hw : s.written = #[]) (text : String) : Turn σ (s.finish text) :=
  .over rfl hw

theorem stopped_over (hvm : s.vm = none) (hw : s.written = #[]) (st : PState Ref) :
    Turn σ (s.stopped st) := by
  unfold Session.stopped
  split <;> first
    | exact finish_over hw _
    | (simp only [Session.ended, hvm]; exact finish_over hw _)

/-- Carrying a turn on keeps the invariant, until the turn saves a function
    every reference of which was made by saving, or ends with nothing stored. -/
theorem advance_turn : ∀ (fuel : Nat) {s : Session}, Inv σ s → Turn σ (advance fuel s)
  | 0, s, h => .over rfl h.written
  | fuel + 1, s, h => by
    obtain ⟨hle, hg, hvm, hnode, hw⟩ := h
    have hg' := hg
    cases hph : s.phase with
    | run st =>
      rw [hph] at hg'
      simp only [advance, hph]
      cases hst : steps s.store s.left st with
      | mk out left =>
        have good := steps_good hle s.left hg' hst
        split
        · rename_i r st' left' heq
          cases heq
          exact .holds ⟨hle, good.2 _ _ rfl, hvm, hnode, hw⟩
        · rename_i v _ heq
          cases heq
          exact advance_turn fuel ⟨hle, good.1 _ rfl, hvm, hnode, hw⟩
        · simp only [hnode]
          exact stopped_over hvm hw _
    | classify v =>
      rw [hph] at hg'
      simp only [advance, hph]
      split
      · exact .holds ⟨hle, hg', hvm, hnode, hw⟩
      · rename_i k _ _ heq
        have hk : Good pieceSize σ k := chase_good hle _ hg' heq
        exact advance_turn fuel ⟨hle, ⟨hk, by simp [GoodS, hk]⟩, hvm, hnode, hw⟩
      · exact advance_turn fuel ⟨hle, trivial, hvm, hnode, hw⟩
    | payload k st =>
      rw [hph] at hg'
      simp only [advance, hph]
      cases hst : steps s.store s.left st with
      | mk out left =>
        have good := steps_good hle s.left hg'.2 hst
        split
        · rename_i r st' left' heq
          cases heq
          exact .holds ⟨hle, ⟨hg'.1, good.2 _ _ rfl⟩, hvm, hnode, hw⟩
        · rename_i v _ heq
          cases heq
          exact advance_turn fuel ⟨hle, hg'.1, hvm, hnode, hw⟩
        · simp only [hnode]
          exact stopped_over hvm hw _
    | ask k p =>
      rw [hph] at hg'
      simp only [advance, hph]
      split
      · exact .holds ⟨hle, hg', hvm, hnode, hw⟩
      · simp only [hnode, hvm]
        exact .waits hg'
      · simp only [hnode, Session.ended, hvm]
        exact finish_over hw _
    | result p =>
      simp only [advance, hph]
      split
      · exact .holds ⟨hle, trivial, hvm, hnode, hw⟩
      · simp only [hnode, Session.ended, hvm]
        exact finish_over hw _
      · exact finish_over hw _
    | resuming r d =>
      rw [hph] at hg'
      simp only [advance, hph]
      obtain ⟨p, hr, hp⟩ := hg'
      split
      · exact .holds ⟨hle, ⟨p, hr, hp⟩, hvm, hnode, hw⟩
      · rename_i p' heq
        cases (hle _ _ heq).symm.trans hr
        exact advance_turn fuel ⟨hle, by simp [PhaseGood, GoodS, hp], hvm, hnode, hw⟩
    | done =>
      simp only [advance, hph]
      exact .over hph hw
    | opening _ => rw [hph] at hg'; exact hg'.elim
    | openingNode _ => rw [hph] at hg'; exact hg'.elim
    | landed _ => rw [hph] at hg'; exact hg'.elim
    | step => rw [hph] at hg'; exact hg'.elim

/-- A session that has seen no piece holds a part of every store. -/
theorem fresh_le {budget left : Nat} {phase : Phase} :
    ({ phase, budget, left } : Session).store.le σ := by
  intro r p h
  simp [Session.store] at h

/-- A program begun from its source: every phase of its first turn holds only
    references that saving made. It holds none. -/
theorem start_turn (src : ByteArray) (budget : Nat) : Turn σ (start src budget) := by
  unfold start
  split
  · exact .over rfl rfl
  · rename_i t _
    have hg : PhaseGood σ (Phase.run (load (compile t)).toP) := by
      simp only [PhaseGood]
      exact goodS_whole _
    exact advance_turn _ ⟨fresh_le, hg, rfl, rfl, rfl⟩

/-- A turn that answers the program under a root, when the piece under the
    root, as a turn holds it, has only references that saving made.
    `Wire.save_opened` says it has, for a root saving gave. -/
theorem answer_turn {root : String} {r : Ref} (hr : unhex root = some r)
    (h : ∃ p, σ r = some p ∧ Good pieceSize σ (opened pieceSize r p)) (src : ByteArray)
    (budget : Nat) : Turn σ (answer root src budget) := by
  unfold answer
  simp only [hr]
  split
  · exact .over rfl rfl
  · split
    · exact advance_turn _ ⟨fresh_le, h, rfl, rfl, rfl⟩
    · exact .over rfl rfl

/-- Supplying a piece. The hypothesis is that the pieces the session holds,
    with the piece read from the bytes among them, are still part of `σ`: that
    the bytes read back to the piece that was written, and that the session's
    map gives back what was put in it. Neither is proved. -/
theorem give_turn {bytes : ByteArray} (h : Inv σ s)
    (hin : ∀ r p, s.need = some r → readPiece bytes = .ok p →
      ∀ x q, (s.pieces.insert r p)[x]? = some q → σ x = some q) :
    Turn σ (give s bytes) := by
  unfold give
  split
  · exact .holds h
  · rename_i r hneed
    split
    · exact .over rfl rfl
    · split
      · exact .over rfl rfl
      · rename_i p hread
        exact advance_turn _
          ⟨fun x q hx => hin r p hneed hread x q hx, h.good, h.vm, h.node, h.written⟩

/-- A turn that ends in a request reports the root of the value held whole:
    the function it saves resolves to a whole value, and is saved under the
    root that value is saved under. -/
theorem waits_root {k : P Ref} (h : Good pieceSize σ k) :
    ∃ q, Unf σ k q ∧ (save pieceSize k).map (·.1) = (save pieceSize q).map (·.1) :=
  good_root h

end Surface.Keep
