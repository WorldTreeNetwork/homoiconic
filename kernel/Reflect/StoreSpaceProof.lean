import Reflect.StoreSpace
import Reflect.StoreProof

/-!
What the priced, space-limited lazy run is proved to do (`bound-kept-sessions`).

It takes `lrun`'s steps: where it ends, `lrun` gets in no more steps than its
fuel, and a pause is at a state whose next step needs the piece it names
(`lrunSpace_ledger`). So `lazy_sound`, `lazy_complete` and the pause theorems
of `StoreProof.lean` speak of what it reaches. The cells its steps made are
within its credit, or within the limit after a state it passed through was
counted at no more than three quarters of it (`lrunSpace_ledger`, `LHeld`). It
stops out of space only when the cells its steps would make pass its credit
(`lrunSpace_full`), so a run whose steps stay within its credit is not
stopped for space whatever the count (`lrunSpace_within`).

These are the plain machine's `runSpace_run`, `runSpace_ledger`,
`runSpace_full` and `runSpace_within` (`SpaceProof.lean`), for the state a run
ends at. They bound the cells a run makes, not what a state holds.
-/

namespace Reflect
variable {R : Type} [Ops]

/-- What the ledger says of the state `k` lazy steps from `s`, with `left` of
    the credit not used: the steps made no more than the credit, or a state
    on the way was counted at no more than `sp.bar` and the steps from it
    made no more than the rest of the limit. -/
def LHeld (σ : Store R) (sp : LSpace R) (credit : Nat) (s : PState R) (k left : Nat) : Prop :=
  lmade σ k s + left ≤ credit ∨
  ∃ j u, j ≤ k ∧ lrun σ j s = .at u ∧ sp.count u ≤ sp.bar ∧
    sp.count u + lmade σ (k - j) u + left ≤ sp.cells

theorem afford_some {sp : LSpace R} {c : Nat} {s : PState R} {a c' : Nat}
    (h : afford sp c s a = some c') :
    (a ≤ c ∧ c' = c - a) ∨
      (sp.count s ≤ sp.bar ∧ a ≤ sp.cells - sp.count s ∧ c' = sp.cells - sp.count s - a) := by
  unfold afford at h
  split at h
  · left; exact ⟨by assumption, (Option.some.inj h).symm⟩
  · split at h
    · rename_i hc; right; exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩
    · cases h

theorem afford_none {sp : LSpace R} {c : Nat} {s : PState R} {a : Nat}
    (h : afford sp c s a = none) : c < a := by
  unfold afford at h
  split at h
  · cases h
  · omega

theorem lmade_next {σ : Store R} {s s' : PState R} (h : lstep σ s = .next s') (n : Nat) :
    lmade σ (n + 1) s = lcharge s s' + lmade σ n s' := by
  simp [lmade, h]

theorem lrun_next {σ : Store R} {s s' : PState R} (h : lstep σ s = .next s') (n : Nat) :
    lrun σ (n + 1) s = lrun σ n s' := by
  simp [lrun, h]

/-- A step afforded at `s`, and the ledger from the state it leads to, give
    the ledger from `s`. -/
theorem LSpace.bar_le (sp : LSpace R) : sp.bar ≤ sp.cells := by
  unfold LSpace.bar; omega

theorem lheld_step {σ : Store R} {sp : LSpace R} {c c2 : Nat} {s s' : PState R}
    (hs : lstep σ s = .next s') (ha : afford sp c s (lcharge s s') = some c2)
    {k left : Nat} (h : LHeld σ sp c2 s' k left) : LHeld σ sp c s (k + 1) left := by
  unfold LHeld at h ⊢
  rw [lmade_next hs]
  have := sp.bar_le
  rcases afford_some ha with ⟨hle, rfl⟩ | ⟨hb, hle, rfl⟩
  · rcases h with h | ⟨j, u, hj, hu, hb, hm⟩
    · left; omega
    · right
      refine ⟨j + 1, u, by omega, by rw [lrun_next hs]; exact hu, hb, ?_⟩
      rw [show k + 1 - (j + 1) = k - j by omega]; exact hm
  · rcases h with h | ⟨j, u, hj, hu, hb', hm⟩
    · right
      refine ⟨0, s, Nat.zero_le _, rfl, hb, ?_⟩
      rw [Nat.sub_zero, lmade_next hs]; omega
    · right
      refine ⟨j + 1, u, by omega, by rw [lrun_next hs]; exact hu, hb', ?_⟩
      rw [show k + 1 - (j + 1) = k - j by omega]; exact hm

theorem lheld_zero (σ : Store R) (sp : LSpace R) (c : Nat) (s : PState R) :
    LHeld σ sp c s 0 c := by
  left; simp [lmade]

/-- Cells afforded and not spent: what a count left is given back. -/
theorem lheld_back {σ : Store R} {sp : LSpace R} {c c1 a : Nat} {s : PState R}
    (h : afford sp c s a = some c1) : LHeld σ sp c s 0 (c1 + a) := by
  have := sp.bar_le
  rcases afford_some h with ⟨hle, rfl⟩ | ⟨hb, hle, rfl⟩
  · left; simp [lmade]; omega
  · right; exact ⟨0, s, Nat.le_refl _, rfl, hb, by simp [lmade]; omega⟩

/-- Where a priced, space-limited lazy run ends, `lrun` gets in no more
    steps than the fuel; a pause is at a state whose next step needs the
    piece it names; and the cells the steps made are within the credit, or
    within the limit after a count (`LHeld`, with the credit left on top). -/
theorem lrunSpace_ledger (σ : Store R) (sp : LSpace R) : ∀ (fuel credit : Nat) (s : PState R),
    ∃ k, k ≤ fuel ∧ lrun σ k s = .at (lrunSpace σ sp fuel credit s).1.state ∧
      (∀ r t, (lrunSpace σ sp fuel credit s).1 = .paused r t → lstep σ t = .needs r) ∧
      LHeld σ sp credit s k (lrunSpace σ sp fuel credit s).2.2 := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro credit s
    have stay : ∀ (e : LEnded R) (left : Nat), e.state = s →
        (∀ r t, e = .paused r t → lstep σ t = .needs r) → LHeld σ sp credit s 0 left →
        ∃ k, k ≤ fuel ∧ lrun σ k s = .at e.state ∧
          (∀ r t, e = .paused r t → lstep σ t = .needs r) ∧ LHeld σ sp credit s k left :=
      fun e left he hp hh => ⟨0, Nat.zero_le _, by rw [he]; rfl, hp, hh⟩
    cases fuel with
    | zero => rw [lrunSpace]; exact stay _ _ rfl (fun _ _ h => by cases h) (lheld_zero σ sp credit s)
    | succ fuel =>
      by_cases hh : (∃ o, s = .halted o) ∨ s = .fault
      · rcases hh with ⟨o, rfl⟩ | rfl <;> rw [lrunSpace] <;>
          exact stay _ _ rfl (fun _ _ h => by cases h) (lheld_zero σ sp _ _)
      · rw [lrunSpace.eq_4 _ _ _ _ _ (fun o h => hh (.inl ⟨o, h⟩)) (fun h => hh (.inr h))]
        split
        · split
          · exact stay _ _ rfl (fun _ _ h => by cases h) (lheld_zero σ sp credit s)
          · rename_i c1 hc1
            split
            · split
              · rename_i r hr
                exact stay _ _ rfl (fun _ _ h => by cases h; exact hr) (lheld_back hc1)
              · rename_i s'' hs
                split
                · rename_i hp
                  split
                  · exact stay _ _ rfl (fun _ _ h => by cases h) (lheld_zero σ sp credit s)
                  · rename_i c2 hc2
                    obtain ⟨k, hk', hl, hpa, hh⟩ := ih (fuel + 1 - max 1 (lstepCostWithin s (fuel + 1))) (by omega) c2 s''
                    refine ⟨k + 1, by omega, by rw [lrun_next hs]; exact hl, hpa, ?_⟩
                    exact lheld_step hs (by simpa [lcharge, hp] using hc2) hh
                · rename_i hp
                  obtain ⟨k, hk', hl, hpa, hh⟩ := ih (fuel + 1 - max 1 (lstepCostWithin s (fuel + 1))) (by omega) c1 s''
                  refine ⟨k + 1, by omega, by rw [lrun_next hs]; exact hl, hpa, ?_⟩
                  exact lheld_step hs (by simpa [lcharge, hp] using hc1) hh
            · exact stay _ _ rfl (fun _ _ h => by cases h) (lheld_back hc1)
        · exact stay _ _ rfl (fun _ _ h => by cases h) (lheld_zero σ sp credit s)

/-- More steps make no fewer cells. -/
theorem lmade_succ_le (σ : Store R) : ∀ (n : Nat) (s : PState R), lmade σ n s ≤ lmade σ (n + 1) s := by
  intro n
  induction n with
  | zero => intro s; simp [lmade]
  | succ n ih =>
    intro s
    cases hs : lstep σ s with
    | next s' => rw [lmade_next hs, lmade_next hs]; have := ih s'; omega
    | needs r => simp [lmade, hs]

theorem lmade_mono (σ : Store R) {n m : Nat} (s : PState R) (h : n ≤ m) : lmade σ n s ≤ lmade σ m s := by
  induction m with
  | zero => cases h; exact Nat.le_refl _
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact Nat.le_trans (ih (by omega)) (lmade_succ_le σ m s)
    · subst h; exact Nat.le_refl _

/-- A run stops out of space at the state `k` steps on only when the cells
    its first `k + 1` steps would make pass its credit. -/
theorem lrunSpace_full (σ : Store R) (sp : LSpace R) : ∀ (fuel credit : Nat) (s t : PState R),
    (lrunSpace σ sp fuel credit s).1 = .full t →
      ∃ k, k < fuel ∧ lrun σ k s = .at t ∧ credit < lmade σ (k + 1) s := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro credit s t h
    have first : ∀ s', lstep σ s = .next s' → credit < lcharge s s' → credit < lmade σ 1 s :=
      fun s' hs hc => by rw [lmade_next hs]; simp only [lmade]; omega
    have later : ∀ s' c', lstep σ s = .next s' → afford sp credit s (lcharge s s') = some c' →
        ∀ k, c' < lmade σ (k + 1) s' → credit < lmade σ (k + 2) s := by
      intro s' c' hs ha k hm
      rw [lmade_next hs]
      unfold afford at ha
      split at ha
      · cases ha; omega
      · rename_i hn
        have := lmade_mono σ s' (Nat.zero_le (k + 1)); omega
    cases fuel with
    | zero => rw [lrunSpace] at h; cases h
    | succ fuel =>
      by_cases hh : (∃ o, s = .halted o) ∨ s = .fault
      · rcases hh with ⟨o, rfl⟩ | rfl <;> rw [lrunSpace] at h <;> cases h
      · rw [lrunSpace.eq_4 _ _ _ _ _ (fun o h => hh (.inl ⟨o, h⟩)) (fun h => hh (.inr h))] at h
        split at h
        · split at h
          · rename_i hc1
            cases h
            refine ⟨0, by omega, rfl, ?_⟩
            have := afford_none hc1
            cases hs : lstep σ s with
            | next s' => exact first s' hs (by simp only [lcharge]; omega)
            | needs r => simp [lmade, hs]; omega
          · rename_i c1 hc1
            split at h
            · split at h
              · cases h
              · rename_i s' hs
                split at h
                · rename_i hp
                  split at h
                  · rename_i hc2
                    cases h
                    refine ⟨0, by omega, rfl, ?_⟩
                    have := afford_none hc2
                    exact first s' hs (by simp only [lcharge, hp, ite_true]; omega)
                  · rename_i c2 hc2
                    obtain ⟨k, hk, hl, hm⟩ := ih (fuel + 1 - max 1 (lstepCostWithin s (fuel + 1))) (by omega) c2 s' t h
                    exact ⟨k + 1, by omega, by rw [lrun_next hs]; exact hl,
                      later s' c2 hs (by simpa [lcharge, hp] using hc2) k hm⟩
                · rename_i hp
                  obtain ⟨k, hk, hl, hm⟩ := ih (fuel + 1 - max 1 (lstepCostWithin s (fuel + 1))) (by omega) c1 s' t h
                  exact ⟨k + 1, by omega, by rw [lrun_next hs]; exact hl,
                    later s' c1 hs (by simpa [lcharge, hp] using hc1) k hm⟩
            · cases h
        · cases h

/-- A run whose first `fuel` steps make no more cells than its credit is not
    stopped for space, whatever the count. -/
theorem lrunSpace_within (σ : Store R) (sp : LSpace R) {fuel credit : Nat} {s : PState R}
    (h : lmade σ fuel s ≤ credit) : ∀ t, (lrunSpace σ sp fuel credit s).1 ≠ .full t := by
  intro t hf
  obtain ⟨k, hk, _, hm⟩ := lrunSpace_full σ sp fuel credit s t hf
  have := lmade_mono σ s (show k + 1 ≤ fuel by omega)
  omega

end Reflect
