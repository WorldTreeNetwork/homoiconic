import Reflect.Crossing
import Reflect.ChannelProof

/-!
What is proved of a combined record.

`accepted_network`: a record the check accepts is a run of the one-machine
network from the program, so every channel theorem holds of it. The check
accepts by replaying; this is `replay_true` applied to the schedule `combine`
gives.

`combine_merged`: the walk does only what the table allows (`Merged`).
`merged_exact`: a walk keeps each log whole and in its order.
`merged_once`: in a walk no crossing is taken twice.

Nothing here is about what a guest does.
-/
namespace Reflect

/-- The walk is one the table allows. -/
theorem mix_walk : ∀ (fuel : Nat) (m : Mix) (a b : List Note) (evs : List Event) (last : Mix),
    mix fuel m a b = some (evs, last) → ∃ tr, Walk m a b tr evs last := by
  intro fuel
  induction fuel with
  | zero =>
    intro m a b evs last h
    cases a with
    | nil =>
      cases b with
      | nil =>
        simp only [mix] at h
        split at h
        · next hs => cases h; exact ⟨[], .done hs⟩
        · cases h
      | cons y ys => simp [mix] at h
    | cons x xs => simp [mix] at h
  | succ fuel ih =>
    intro m a b evs last h
    cases a with
    | nil =>
      cases b with
      | nil =>
        simp only [mix] at h
        split at h
        · next hs => cases h; exact ⟨[], .done hs⟩
        · cases h
      | cons y ys =>
        simp only [mix] at h
        split at h
        · next m' es hp =>
          cases hr : mix fuel m' [] ys with
          | none => simp [hr] at h
          | some r =>
            obtain ⟨es', last'⟩ := r
            simp [hr] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨tr, hw⟩ := ih m' [] ys es' last' hr
            exact ⟨_, .right hp hw⟩
        · cases h
    | cons x xs =>
      simp only [mix] at h
      split at h
      · next m' es hp =>
        cases hr : mix fuel m' xs b with
        | none => simp [hr] at h
        | some r =>
          obtain ⟨es', last'⟩ := r
          simp [hr] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨tr, hw⟩ := ih m' xs b es' last' hr
          exact ⟨_, .left hp hw⟩
      · split at h
        · next y ys' =>
          split at h
          · next m' es hp =>
            cases hr : mix fuel m' (x :: xs) ys' with
            | none => simp [hr] at h
            | some r =>
              obtain ⟨es', last'⟩ := r
              simp [hr] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨tr, hw⟩ := ih m' (x :: xs) ys' es' last' hr
              exact ⟨_, .right hp hw⟩
          · cases h
        · cases h

/-- What `combine` gives is a schedule the table allows. -/
theorem combine_merged {a b : List Note} {evs : List Event} (h : combine a b = some evs) :
    Merged a b evs := by
  unfold combine combineMix at h
  cases hr : mix (a.length + b.length) Mix.first a b with
  | none => simp [hr] at h
  | some r =>
    obtain ⟨es, last⟩ := r
    simp [hr] at h
    subst h
    obtain ⟨tr, hw⟩ := mix_walk _ _ _ _ _ _ hr
    exact ⟨tr, last, hw⟩

/-- A walk keeps each log whole and in its order: the entries of `a` among
    those placed are `a`, and those of `b` are `b`. -/
theorem Walk.exact {m last : Mix} {a b : List Note} {tr : List (Side × Note)}
    {evs : List Event} (h : Walk m a b tr evs last) :
    entriesOf .a tr = a ∧ entriesOf .b tr = b := by
  induction h with
  | done _ => exact ⟨rfl, rfl⟩
  | left _ _ ih => exact ⟨by simp [entriesOf] at ih ⊢; exact ih.1, by simp [entriesOf] at ih ⊢; exact ih.2⟩
  | right _ _ ih => exact ⟨by simp [entriesOf] at ih ⊢; exact ih.1, by simp [entriesOf] at ih ⊢; exact ih.2⟩

theorem merged_exact {a b : List Note} {evs : List Event} (h : Merged a b evs) :
    ∃ tr, entriesOf .a tr = a ∧ entriesOf .b tr = b := by
  obtain ⟨tr, _, hw⟩ := h
  exact ⟨tr, hw.exact⟩

theorem Mix.outs_setOuts_same (m : Mix) (s : Side) (cs : List Crossing) :
    (m.setOuts s cs).outs s = cs := by cases s <;> rfl

theorem Mix.outs_setOuts_other (m : Mix) {s u : Side} (cs : List Crossing) (h : u ≠ s) :
    (m.setOuts s cs).outs u = m.outs u := by
  cases s <;> cases u <;> first | rfl | exact absurd rfl h

theorem Mix.outs_grow (m : Mix) (s u : Side) : (m.grow s).outs u = m.outs u := by
  cases s <;> cases u <;> rfl

/-- What placing an entry does to a guest's crossings: nothing, one more
    offered at the end, or one moved on from `offered`. -/
inductive Moved (old new : List Crossing) : Prop where
  | same (h : new = old)
  | more (g : Nat) (h : new = old ++ [⟨g, .offered⟩])
  | on (k g : Nat) (st : Crossed) (hs : st ≠ .offered) (h : new = old.set k ⟨g, st⟩)

theorem Mix.setOuts_moved (m : Mix) (s u : Side) {cs : List Crossing}
    (h : Moved (m.outs s) cs) : Moved (m.outs u) ((m.setOuts s cs).outs u) := by
  by_cases hu : u = s
  · subst hu; rw [Mix.outs_setOuts_same]; exact h
  · rw [Mix.outs_setOuts_other m cs hu]; exact .same rfl

theorem Mix.place_moved {m m' : Mix} {t : Side} {e : Note} {evs : List Event}
    (h : m.place t e = some (m', evs)) (u : Side) : Moved (m.outs u) (m'.outs u) := by
  cases e with
  | did ev =>
    cases ev with
    | fresh i n =>
      simp only [Mix.place] at h
      cases hf : m.free t i <;> simp [hf] at h
      obtain ⟨rfl, _⟩ := h; exact .same rfl
    | spawn i =>
      simp only [Mix.place] at h
      cases hf : m.free t i <;> simp [hf] at h
      obtain ⟨rfl, _⟩ := h; exact .same (Mix.outs_grow m t u)
    | comm i j =>
      simp only [Mix.place] at h
      split at h
      · cases h; exact .same rfl
      · cases h
    | answer i x =>
      simp only [Mix.place] at h
      cases hf : m.free t i <;> simp [hf] at h
      obtain ⟨rfl, _⟩ := h; exact .same rfl
  | out i k =>
    simp only [Mix.place] at h
    split at h
    · next g _ =>
      split at h
      · cases h; exact Mix.setOuts_moved m t u (.more g rfl)
      · cases h
    · cases h
  | spawnIn k =>
    simp only [Mix.place] at h
    split at h
    · next g _ =>
      cases h
      rw [Mix.outs_grow]
      exact Mix.setOuts_moved m t.other u (.on k g .taken (by decide) rfl)
    · cases h
  | sendIn k j =>
    simp only [Mix.place] at h
    split at h
    · next g _ _ _ =>
      cases h
      exact Mix.setOuts_moved m t.other u (.on k g .taken (by decide) rfl)
    · cases h
  | ack k i =>
    simp only [Mix.place] at h
    split at h
    · next g g' _ _ =>
      split at h
      · cases h; exact Mix.setOuts_moved m t u (.on k g .acked (by decide) rfl)
      · cases h
    · cases h

/-- A crossing that has moved on from `offered` stays so. -/
theorem Moved.keeps {old new : List Crossing} (h : Moved old new) {k : Nat} {c : Crossing}
    (hk : old[k]? = some c) (hc : c.state ≠ .offered) :
    ∃ c', new[k]? = some c' ∧ c'.state ≠ .offered := by
  have hlt : k < old.length := by
    cases hlt : decide (k < old.length) with
    | true => exact of_decide_eq_true hlt
    | false =>
      have := of_decide_eq_false hlt
      rw [List.getElem?_eq_none (Nat.le_of_not_lt this)] at hk; cases hk
  cases h with
  | same h => subst h; exact ⟨c, hk, hc⟩
  | more g h => subst h; exact ⟨c, by rw [List.getElem?_append_left hlt]; exact hk, hc⟩
  | on j g st hs h =>
    subst h
    by_cases hj : j = k
    · subst hj
      exact ⟨⟨g, st⟩, by rw [List.getElem?_set_self hlt], hs⟩
    · exact ⟨c, by rw [List.getElem?_set_ne hj]; exact hk, hc⟩

/-- The crossing of guest `u` numbered `k` has not moved on from `offered`. -/
def Mix.Fresh (m : Mix) (u : Side) (k : Nat) : Prop :=
  ∀ c, (m.outs u)[k]? = some c → c.state = .offered

theorem Mix.place_fresh {m m' : Mix} {t : Side} {e : Note} {evs : List Event}
    (h : m.place t e = some (m', evs)) {u : Side} {k : Nat} (hf : m'.Fresh u k) : m.Fresh u k := by
  intro c hc
  cases hs : c.state with
  | offered => rfl
  | taken =>
    obtain ⟨c', hc', hn⟩ := (Mix.place_moved h u).keeps hc (by rw [hs]; decide)
    exact absurd (hf c' hc') hn
  | acked =>
    obtain ⟨c', hc', hn⟩ := (Mix.place_moved h u).keeps hc (by rw [hs]; decide)
    exact absurd (hf c' hc') hn

/-- Placing a taking entry of guest `s` needs the crossing offered, and leaves
    it not offered. -/
theorem Mix.place_takes {m m' : Mix} {s : Side} {e : Note} {evs : List Event} {k : Nat}
    (h : m.place s e = some (m', evs))
    (he : e.taking = some k) :
    m.Fresh s.other k ∧ ¬ m'.Fresh s.other k := by
  cases e with
  | did ev => cases he
  | out i k' => cases he
  | ack k' i => cases he
  | spawnIn k' =>
    cases he
    simp only [Mix.place] at h
    split at h
    · next g hg =>
      cases h
      refine ⟨fun c hc => by rw [hg] at hc; cases hc; rfl, fun hf => ?_⟩
      have hlt : k < (m.outs s.other).length := by
        cases hlt : decide (k < (m.outs s.other).length) with
        | true => exact of_decide_eq_true hlt
        | false =>
          rw [List.getElem?_eq_none (Nat.le_of_not_lt (of_decide_eq_false hlt))] at hg; cases hg
      have := hf ⟨g, .taken⟩ (by
        rw [Mix.outs_grow, Mix.outs_setOuts_same, List.getElem?_set_self hlt])
      cases this
    · cases h
  | sendIn k' j =>
    cases he
    simp only [Mix.place] at h
    split at h
    · next g _ hg _ =>
      cases h
      refine ⟨fun c hc => by rw [hg] at hc; cases hc; rfl, fun hf => ?_⟩
      have hlt : k < (m.outs s.other).length := by
        cases hlt : decide (k < (m.outs s.other).length) with
        | true => exact of_decide_eq_true hlt
        | false =>
          rw [List.getElem?_eq_none (Nat.le_of_not_lt (of_decide_eq_false hlt))] at hg; cases hg
      have := hf ⟨g, .taken⟩ (by
        rw [Mix.outs_setOuts_same, List.getElem?_set_self hlt])
      cases this
    · cases h

theorem once_step {m m' : Mix} {t s : Side} {e : Note} {evs : List Event} {tr : List (Side × Note)}
    (hp : m.place t e = some (m', evs))
    (ih : (takenBy s tr).Nodup ∧ ∀ k ∈ takenBy s tr, m'.Fresh s.other k) :
    (takenBy s ((t, e) :: tr)).Nodup ∧ ∀ k ∈ takenBy s ((t, e) :: tr), m.Fresh s.other k := by
  have back : ∀ k ∈ takenBy s tr, m.Fresh s.other k := fun k hk => Mix.place_fresh hp (ih.2 k hk)
  by_cases hts : t = s
  · subst hts
    cases hk : e.taking with
    | none =>
      have : takenBy t ((t, e) :: tr) = takenBy t tr := by
        simp [takenBy, hk]
      rw [this]; exact ⟨ih.1, back⟩
    | some k =>
      have : takenBy t ((t, e) :: tr) = k :: takenBy t tr := by
        simp [takenBy, hk]
      rw [this]
      obtain ⟨hf, hn⟩ := Mix.place_takes hp hk
      refine ⟨List.nodup_cons.mpr ⟨fun hin => hn (ih.2 k hin), ih.1⟩, ?_⟩
      intro k' hk'
      cases List.mem_cons.mp hk' with
      | inl h => subst h; exact hf
      | inr h => exact back k' h
  · have : takenBy s ((t, e) :: tr) = takenBy s tr := by
      simp [takenBy, hts]
    rw [this]; exact ⟨ih.1, back⟩


/-- In a walk no crossing is taken twice: the crossings guest `s` took are all
    different, and none had been taken before the walk began. -/
theorem Walk.once {m last : Mix} {a b : List Note} {tr : List (Side × Note)}
    {evs : List Event} (h : Walk m a b tr evs last) (s : Side) :
    (takenBy s tr).Nodup ∧ ∀ k ∈ takenBy s tr, m.Fresh s.other k := by
  induction h with
  | done _ => exact ⟨List.nodup_nil, fun k hk => by simp [takenBy] at hk⟩
  | @left m m' x xs ys tr evs evs' last hp _ ih =>
    exact once_step hp ih
  | @right m m' y xs ys tr evs evs' last hp _ ih =>
    exact once_step hp ih

theorem merged_once {a b : List Note} {evs : List Event} (h : Merged a b evs) :
    ∃ tr, entriesOf .a tr = a ∧ entriesOf .b tr = b ∧
      (takenBy .a tr).Nodup ∧ (takenBy .b tr).Nodup := by
  obtain ⟨tr, _, hw⟩ := h
  exact ⟨tr, hw.exact.1, hw.exact.2, (hw.once .a).1, (hw.once .b).1⟩

variable [Ops]

/-- When every event of a schedule happened, the events reported are the
    schedule. -/
theorem schedRun_ran {budget : Nat} : ∀ (evs : List Event) (cfg : MConfig),
    (schedRun budget cfg evs).2.2 = .ran → (schedRun budget cfg evs).1 = evs := by
  intro evs
  induction evs with
  | nil => intro cfg _; rfl
  | cons ev evs ih =>
    intro cfg h
    rw [schedRun] at h ⊢
    split
    · next mid hm =>
      rw [hm] at h
      simp only at h ⊢
      rw [ih mid h]
    · next hm => rw [hm] at h; cases h
    · next hm => rw [hm] at h; cases h

/-- An accepted record is a run of the one-machine network: the schedule the
    two logs make leads the program, by direct evaluation, to a configuration
    whose compiled form is the one the check reports. -/
theorem accepted_network {budget : Nat} {p : Term} {a b : List Note} {evs : List Event}
    {cfg : MConfig} (h : accept budget p a b = some (evs, cfg)) :
    Merged a b evs ∧ ∃ c, Network sourceP p evs c ∧ cfg = c.map MP.injO MP.injV := by
  unfold accept at h
  split at h
  · next es c₀ hc hb =>
    split at h
    · next done cfg' hr =>
      cases h
      refine ⟨combine_merged hc, ?_⟩
      obtain ⟨c, hn, he⟩ := replay_true (budget := budget) evs hb
      have hran : (schedRun budget c₀ evs).2.2 = .ran := by rw [hr]
      rw [schedRun_ran evs c₀ hran] at hn
      rw [hr] at he
      exact ⟨c, hn, (he : cfg = _)⟩
    · cases h
  · cases h

end Reflect
