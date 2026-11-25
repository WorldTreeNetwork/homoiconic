import Reflect.Hold
import Reflect.CrossingProof

/-!
What is proved of the ledger of a crossing.

The measured runs are the runs: each gives, as its first part, exactly what
`runSpace`, `runTurnIn`, `settleIn`, `turnIn`, `beginIn` and `stepIn` give
(`runSpaceLeft_fst` to `stepMade_fst`). The check's replay of a trace is
`schedIn` on the trace's events (`traceRun_sched`), so `accepted_network`
speaks of what the check ran. And of the walk of one side's ledger
(`holdGo`, `holdWalk`): between two counts the side charged no more than the
credit it had, beyond the entry that spent it (`hold_stretch`); a count it
went on from is at most the bar and the next stretch has the hold less the
count (`hold_count`); after `full` come only acknowledgements, at most
`outLimit` (`hold_full`); and a side has at most `entryLimit + outLimit + 1`
entries (`hold_entries`).
-/
namespace Reflect

variable [Ops]

theorem runSpaceLeft_fst (sp : Space) : ∀ (fuel credit : Nat) (s : State),
    (runSpaceLeft sp fuel credit s).1 = runSpace sp fuel credit s := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro credit s
    cases fuel with
    | zero => rw [runSpaceLeft, runSpace]
    | succ f =>
      cases s with
      | halted o => rw [runSpaceLeft, runSpace]
      | fault => rw [runSpaceLeft, runSpace]
      | running c e stk frs =>
        rw [runSpaceLeft, runSpace]
        repeat' split
        all_goals first | rfl | (apply ih; omega)

theorem runTurnMade_fst (cells budget : Nat) (s : State) :
    (runTurnMade cells budget s).1 = runTurnIn cells budget s := by
  simp only [runTurnMade, runTurnIn, runIn, runSpaceLeft_fst]
  rfl

theorem settleMade_fst (cells budget : Nat) (w : MOutcome) :
    (settleMade cells budget w).1 = settleIn cells budget w := by
  rcases w with (⟨k, e⟩ | d) | i | _ <;> simp [settleMade, settleIn, runTurnMade_fst] <;> rfl

theorem turnMade_fst (cells budget : Nat) (c : MValue) (a : Data) :
    (turnMade cells budget c a).1 = turnIn cells budget c a := by
  simp only [turnMade, turnIn]
  rw [← runTurnMade_fst]
  generalize (runTurnMade cells budget (.running (compile (resumeTerm a)) [c] [] [])) = r
  obtain ⟨st, n⟩ := r
  cases st <;> simp [settleMade_fst]

theorem beginMade_fst (cells budget : Nat) (p : Term) :
    (beginMade cells budget p).1 = beginIn cells budget p := by
  simp only [beginMade, beginIn]
  rw [← runTurnMade_fst]
  generalize (runTurnMade cells budget (load (compile p))) = r
  obtain ⟨st, n⟩ := r
  cases st with
  | halted w =>
    simp only [← settleMade_fst]
    generalize settleMade cells budget w = q
    obtain ⟨o, m⟩ := q
    cases o <;> rfl
  | _ => rfl

theorem stepMade_fst (cells budget : Nat) (cfg : MConfig) (ev : Event) :
    (stepMade cells budget cfg ev).1 = stepIn cells budget cfg ev := by
  cases ev <;> simp only [stepMade, stepIn] <;>
    (repeat' (split <;> (try simp only [*, turnMade_fst, settleMade_fst, runTurnMade_fst] at *))) <;>
    first | rfl | simp_all

/-- The measured run of a list of events is `schedIn`'s. -/
theorem runEvents_sched (cells budget : Nat) : ∀ (cfg : MConfig) (evs : List Event),
    ((runEvents cells budget cfg evs).1, (runEvents cells budget cfg evs).2.1,
      (runEvents cells budget cfg evs).2.2.1) = schedIn cells budget cfg evs := by
  intro cfg evs
  induction evs generalizing cfg with
  | nil => rfl
  | cons ev evs ih =>
    rw [runEvents, schedIn, ← stepMade_fst]
    split
    · next mid hm => simp only [hm]; rw [← ih mid]
    · next hm => simp only [hm]
    · next hm => simp only [hm]

theorem schedIn_append (cells budget : Nat) : ∀ (cfg mid : MConfig) (xs ys : List Event),
    schedIn cells budget cfg xs = (xs, mid, .ran) →
    schedIn cells budget cfg (xs ++ ys) =
      (xs ++ (schedIn cells budget mid ys).1, (schedIn cells budget mid ys).2) := by
  intro cfg mid xs ys h
  induction xs generalizing cfg with
  | nil => simp [schedIn] at h; obtain ⟨rfl⟩ := h; rfl
  | cons x xs ih =>
    rw [schedIn] at h
    simp only [List.cons_append]
    rw [schedIn]
    split at h
    · next m hm =>
      simp only [hm]
      have h' : schedIn cells budget m xs = (xs, mid, .ran) := by
        cases hr : schedIn cells budget m xs with
        | mk a b =>
          rw [hr] at h
          simp at h
          obtain ⟨h1, h2⟩ := h
          cases b; simp_all
      rw [ih m h']
    · cases h
    · cases h

/-- When the check's replay runs every event of a trace, its events and its
    configuration are those of `schedIn` on the trace's events. -/
theorem traceRun_sched (cells budget : Nat) (places : Side → List Nat) :
    ∀ (t : List (Side × Note × List Event)) (cfg : MConfig) (pa pb : Nat),
    (traceRun cells budget places cfg pa pb t).stopped = .ran →
    schedIn cells budget cfg (traceEvents t) =
      ((traceRun cells budget places cfg pa pb t).events, (traceRun cells budget places cfg pa pb t).cfg,
        .ran) := by
  intro t
  induction t with
  | nil => intro cfg pa pb _; rfl
  | cons e rest ih =>
    obtain ⟨s, n, evs⟩ := e
    intro cfg pa pb h
    have hte : traceEvents ((s, n, evs) :: rest) = evs ++ traceEvents rest := by
      simp [traceEvents]
    rw [hte]
    rw [traceRun] at h ⊢
    cases hf : evs.find? isAnswer with
    | some ev => simp only [hf] at h; cases h
    | none =>
      simp only [hf] at h ⊢
      have hq := runEvents_sched cells budget cfg evs
      generalize runEvents cells budget cfg evs = q at hq h ⊢
      obtain ⟨evs', mid, stop, x, y⟩ := q
      simp only at hq h ⊢
      cases stop with
      | refused ev => cases h
      | unfinished ev => cases h
      | ran =>
        have hran : (schedIn cells budget cfg evs).2.2 = .ran := by rw [← hq]
        have he : evs' = evs := by
          have := schedIn_ran evs cfg hran
          rw [← hq] at this; exact this
        subst he
        rw [schedIn_append cells budget cfg mid evs' (traceEvents rest) hq.symm]
        cases s with
        | a =>
          simp only at h ⊢
          rw [ih _ _ _ h]
        | b =>
          simp only at h ⊢
          rw [ih _ _ _ h]

end Reflect

namespace Reflect

/-! The ledger walk. -/

theorem afterFull_acks {k : Nat} {rest : List Charged} (h : afterFull k rest = .ok ()) :
    (∀ e ∈ rest, e.note.isAck = true) ∧ rest.length ≤ outLimit := by
  unfold afterFull at h
  split at h
  · cases h
  · next hn =>
    split at h
    · next hl =>
      refine ⟨fun e he => ?_, hl⟩
      have := List.findIdx?_eq_none_iff.mp hn e he
      simpa using this
    · cases h

/-- What one step of the walk does with an entry that is not a count. -/
theorem holdGo_plain {hold k credit : Nat} {must cap : Bool} {e : Charged} {rest : List Charged}
    {r : Option (Nat × Nat)} (hc : e.note.isCount = false)
    (h : holdGo hold k credit must cap (e :: rest) = .ok r) :
    must = false ∧
      ((e.cost ≤ credit ∧ ¬(entryLimit ≤ k + 1 ∨ procLimit ≤ e.procs) ∧
          holdGo hold (k + 1) (credit - e.cost) false false rest = .ok r) ∨
        holdGo hold (k + 1) credit true (entryLimit ≤ k + 1 || procLimit ≤ e.procs) rest = .ok r) := by
  rw [holdGo] at h
  cases hn : e.note <;> rw [hn] at h hc <;> simp [Note.isCount] at hc <;>
  · simp only at h
    split at h
    · cases h
    · next hm =>
      simp at hm
      refine ⟨hm, ?_⟩
      split at h
      · next hcr =>
        simp at hcr
        exact .inl ⟨hcr.1, by simpa using hcr.2, h⟩
      · exact .inr h

/-- Between the start, or a count, and the next count, the entries but the
    last charged no more than the credit the stretch began with. -/
theorem hold_stretch (hold : Nat) : ∀ (seg rest : List Charged) (k credit : Nat)
    (r : Option (Nat × Nat)),
    holdGo hold k credit false false (seg ++ rest) = .ok r →
    (∀ e ∈ seg, e.note.isCount = false) →
    ((seg.dropLast).map (·.cost)).sum ≤ credit := by
  intro seg
  induction seg with
  | nil => intro _ _ _ _ _ _; simp
  | cons e seg ih =>
    intro rest k credit r h hc
    cases seg with
    | nil => simp
    | cons e2 seg' =>
      have hce : e.note.isCount = false := hc e (by simp)
      obtain ⟨_, hp⟩ := holdGo_plain hce h
      rcases hp with ⟨hle, _, h'⟩ | h'
      · have := ih rest (k + 1) (credit - e.cost) r h' (fun x hx => hc x (by simp [hx]))
        simp [List.dropLast] at this ⊢
        omega
      · have hc2 : e2.note.isCount = false := hc e2 (by simp)
        have := (holdGo_plain hc2 h').1
        cases this

/-- The walk reaches every entry of a side's list that is not an
    acknowledgement after `full`: there it is in some state. -/
theorem holdGo_at (hold : Nat) : ∀ (pre : List Charged) (x : Charged) (rest : List Charged)
    (k credit : Nat) (must cap : Bool) (r : Option (Nat × Nat)),
    x.note.isAck = false →
    holdGo hold k credit must cap (pre ++ x :: rest) = .ok r →
    ∃ k' credit' must' cap' r', holdGo hold k' credit' must' cap' (x :: rest) = .ok r' := by
  intro pre
  induction pre with
  | nil => intro x rest k credit must cap r _ h; exact ⟨_, _, _, _, _, h⟩
  | cons p pre ih =>
    intro x rest k credit must cap r hx h
    simp only [List.cons_append] at h
    cases hn : p.note.isCount with
    | false =>
      obtain ⟨_, hp⟩ := holdGo_plain hn h
      rcases hp with ⟨_, _, h'⟩ | h'
      · exact ih x rest _ _ _ _ _ hx h'
      · exact ih x rest _ _ _ _ _ hx h'
    | true =>
      rw [holdGo] at h
      cases hpn : p.note <;> rw [hpn] at h hn <;> simp [Note.isCount] at hn
      · next m =>
        simp only at h
        split at h; · cases h
        split at h; · cases h
        split at h; · cases h
        exact ih x rest _ _ _ _ _ hx h
      · next m =>
        simp only at h
        split at h; · cases h
        split at h; · cases h
        cases ha : afterFull (k + 1) (pre ++ x :: rest) with
        | error _ => rw [ha] at h; cases h
        | ok u =>
          have := (afterFull_acks ha).1 x (by simp)
          rw [hx] at this; cases this

/-- A count the walk goes on from is at most the bar, and the next stretch
    begins with the hold less the count. -/
theorem hold_count {hold k credit : Nat} {must cap : Bool} {r : Option (Nat × Nat)}
    {pre rest : List Charged} {m c ps : Nat}
    (h : holdGo hold k credit must cap (pre ++ ⟨.held m, c, ps⟩ :: rest) = .ok r) :
    m ≤ holdBar hold ∧ ∃ k' r', holdGo hold k' (hold - m) false false rest = .ok r' := by
  obtain ⟨k', _, _, _, r', h'⟩ := holdGo_at hold pre _ rest k credit must cap r rfl h
  rw [holdGo] at h'
  simp only at h'
  split at h'; · cases h'
  split at h'; · cases h'
  split at h'; · cases h'
  next hb => exact ⟨by omega, _, _, h'⟩

/-- After `full` come only acknowledgements, at most `outLimit` of them. -/
theorem hold_full {hold k credit : Nat} {must cap : Bool} {r : Option (Nat × Nat)}
    {pre rest : List Charged} {m c ps : Nat}
    (h : holdGo hold k credit must cap (pre ++ ⟨.full m, c, ps⟩ :: rest) = .ok r) :
    (∀ e ∈ rest, e.note.isAck = true) ∧ rest.length ≤ outLimit := by
  obtain ⟨k', _, _, _, r', h'⟩ := holdGo_at hold pre _ rest k credit must cap r rfl h
  rw [holdGo] at h'
  simp only at h'
  split at h'; · cases h'
  split at h'; · cases h'
  cases ha : afterFull (k' + 1) rest with
  | error _ => rw [ha] at h'; cases h'
  | ok u => exact afterFull_acks ha

/-- How far the walk may be: an entry that is not a count at place `k`
    leaves `k + 1`; past `entryLimit` the walk owes `full`. -/
def HoldInv (k : Nat) (must cap : Bool) : Prop :=
  (must = false → k ≤ entryLimit) ∧ (must = true → cap = false → k < entryLimit) ∧
    k ≤ entryLimit + 1

theorem holdGo_length (hold : Nat) : ∀ (es : List Charged) (k credit : Nat) (must cap : Bool)
    (r : Option (Nat × Nat)), HoldInv k must cap →
    holdGo hold k credit must cap es = .ok r → es.length + k ≤ entryLimit + outLimit + 2 := by
  intro es
  induction es with
  | nil =>
    intro k credit must cap r hi h
    rw [holdGo] at h
    cases must with
    | true => cases h
    | false => have := hi.1 rfl; simp; omega
  | cons e rest ih =>
    intro k credit must cap r hi h
    cases hn : e.note.isCount with
    | false =>
      obtain ⟨hm, hp⟩ := holdGo_plain hn h
      subst hm
      have hk := hi.1 rfl
      rcases hp with ⟨_, hcap, h'⟩ | h'
      · have := ih (k + 1) _ false false r ⟨fun _ => by omega, by simp, by omega⟩ h'
        simp; omega
      · have := ih (k + 1) _ true _ r ⟨by simp, fun _ hc => by simp at hc; omega,
          by omega⟩ h'
        simp; omega
    | true =>
      rw [holdGo] at h
      cases hen : e.note <;> rw [hen] at h hn <;> simp [Note.isCount] at hn
      · next m =>
        simp only at h
        split at h; · cases h
        split at h; · cases h
        split at h; · cases h
        next hmust hcap _ =>
          simp at hmust hcap
          have hk := hi.2.1 hmust hcap
          have := ih (k + 1) _ false false r ⟨fun _ => by omega, by simp, by omega⟩ h
          simp; omega
      · next m =>
        simp only at h
        split at h; · cases h
        split at h; · cases h
        cases ha : afterFull (k + 1) rest with
        | error _ => rw [ha] at h; cases h
        | ok u =>
          have := (afterFull_acks ha).2
          have := hi.2.2
          simp; omega

/-- A side the walk accepts has at most `entryLimit + outLimit + 2` entries. -/
theorem hold_entries {hold first : Nat} {es : List Charged} {r : Option (Nat × Nat)}
    (h : holdWalk hold first es = .ok r) : es.length ≤ entryLimit + outLimit + 2 := by
  unfold holdWalk at h
  split at h
  · have := holdGo_length hold es 0 _ false false r ⟨fun _ => by simp [entryLimit], by simp,
      by simp [entryLimit]⟩ h
    omega
  · have := holdGo_length hold es 0 _ true false r ⟨by simp, fun _ _ => by simp [entryLimit],
      by simp [entryLimit]⟩ h
    omega

end Reflect
