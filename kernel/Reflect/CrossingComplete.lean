import Reflect.CrossingProof

/-!
The greedy walk is complete: when two logs have any schedule the table allows
(`Merged`), `combine` finds one (`combine_complete`).

The walk's state (`Mix`) numbers the processes in the order the walk meets
them, so two orders of the same entries reach states that differ by a
renumbering. What decides whether an entry can be placed does not depend on
the numbers. A `Shape` keeps only that: for each guest how many processes it
has and its crossings, each with the *local* place of the process that asked
and how far it has got. A `Mix` and its shape place the same entries
(`Shaped.place`, `Shaped.back`).

On shapes a guest's entry does two things: something to its own half (`own`)
and, when it takes a crossing, a step of the other guest's half (`take`). An
entry of `a` and an entry of `b` therefore touch each half once from each
side, and on one half an `own` and a `take` that can both be done commute
(`Half.diamond`). So placing an entry never makes an entry of the other guest
unplaceable, and never changes what it does (`Shape.diamond`): whenever some
path exists and the head of `a` can be placed, a path exists after placing it
(`SPath.push`). That is all the greedy walk needs.
-/
namespace Reflect

/-- A crossing without the global numbering: the local place of the process
    that asked, and how far it has got. -/
structure SCross where
  asker : Nat
  state : Crossed

/-- One guest's half of a shape: how many processes it has, and its
    crossings. -/
structure Half where
  n : Nat
  outs : List SCross

structure Shape where
  a : Half
  b : Half

def Shape.half (sh : Shape) : Side → Half
  | .a => sh.a
  | .b => sh.b

def Shape.setHalf (sh : Shape) : Side → Half → Shape
  | .a, h => { sh with a := h }
  | .b, h => { sh with b := h }

/-- Guest `a` has one process, `b` none, and no crossing. -/
def Shape.first : Shape := ⟨⟨1, []⟩, ⟨0, []⟩⟩

/-- The process at local place `i` asked for a crossing not yet acknowledged. -/
def Half.held (h : Half) (i : Nat) : Bool :=
  h.outs.any (fun c => c.asker == i && decide (c.state ≠ .acked))

def Half.free (h : Half) (i : Nat) : Bool := decide (i < h.n) && !h.held i

/-- What an entry does to its own guest's half. -/
inductive OwnOp where
  /-- These places are free; one more process when `grow`. -/
  | free (places : List Nat) (grow : Bool)
  | out (i k : Nat)
  | ack (k i : Nat)

def Note.own : Note → OwnOp
  | .did (.fresh i _) => .free [i] false
  | .did (.spawn i) => .free [i] true
  | .did (.comm i j) => .free [i, j] false
  | .did (.answer i _) => .free [i] false
  | .out i k => .out i k
  | .spawnIn _ => .free [] true
  | .sendIn _ j => .free [j] false
  | .ack k i => .ack k i
  | .held _ => .free [] false
  | .full _ => .free [] false

def Half.own (h : Half) : OwnOp → Option Half
  | .free places grow =>
    if places.all h.free then some (if grow then { h with n := h.n + 1 } else h) else none
  | .out i k =>
    if h.free i && k == h.outs.length then some { h with outs := h.outs ++ [⟨i, .offered⟩] }
    else none
  | .ack k i =>
    match h.outs[k]? with
    | some ⟨i', .taken⟩ =>
      if i' = i ∧ i < h.n then some { h with outs := h.outs.set k ⟨i', .acked⟩ } else none
    | _ => none

/-- The other guest takes this half's crossing `k`, or takes nothing. -/
def Half.take (h : Half) : Option Nat → Option Half
  | none => some h
  | some k =>
    match h.outs[k]? with
    | some ⟨i, .offered⟩ => some { h with outs := h.outs.set k ⟨i, .taken⟩ }
    | _ => none

/-- Place one entry of guest `s` on a shape. -/
def Shape.place (sh : Shape) (s : Side) (e : Note) : Option Shape :=
  match (sh.half s).own e.own, (sh.half s.other).take e.taking with
  | some h, some h' => some ((sh.setHalf s h).setHalf s.other h')
  | _, _ => none

def Shape.settled (sh : Shape) : Bool :=
  (sh.a.outs ++ sh.b.outs).all (fun c => decide (c.state ≠ .taken))

/-- Entries placed one after another, in any order that keeps each log's own;
    nothing is asked of the last shape. -/
inductive SPath : Shape → List Note → List Note → Shape → Prop where
  | done {sh} : SPath sh [] [] sh
  | left {sh sh' x xs ys fin} (h : sh.place .a x = some sh') (rest : SPath sh' xs ys fin) :
      SPath sh (x :: xs) ys fin
  | right {sh sh' y xs ys fin} (h : sh.place .b y = some sh') (rest : SPath sh' xs ys fin) :
      SPath sh xs (y :: ys) fin

/-! One half: an `own` and a `take` commute. -/

theorem Half.held_set_taken {h : Half} {k i : Nat} (hk : h.outs[k]? = some ⟨i, .offered⟩) (j : Nat) :
    Half.held { h with outs := h.outs.set k ⟨i, .taken⟩ } j = h.held j := by
  have hlt : k < h.outs.length := by
    rcases Nat.lt_or_ge k h.outs.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hk; cases hk
  have hget : h.outs[k] = ⟨i, .offered⟩ := by
    rw [List.getElem?_eq_getElem hlt] at hk; exact Option.some.inj hk
  simp only [Half.held]
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hp⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hc
    rw [List.length_set] at hn
    by_cases hnk : k = n
    · subst hnk
      rw [List.getElem_set_self] at hp
      exact ⟨h.outs[k], List.getElem_mem hlt, by rw [hget]; simpa using hp⟩
    · rw [List.getElem_set_ne hnk] at hp
      exact ⟨h.outs[n], List.getElem_mem hn, hp⟩
  · rintro ⟨c, hc, hp⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hc
    by_cases hnk : k = n
    · subst hnk
      refine ⟨⟨i, .taken⟩, ?_, ?_⟩
      · exact List.mem_iff_getElem.mpr ⟨k, by rw [List.length_set]; exact hlt, by
          rw [List.getElem_set_self]⟩
      · rw [hget] at hp; simpa using hp
    · refine ⟨h.outs[n], ?_, hp⟩
      exact List.mem_iff_getElem.mpr ⟨n, by rw [List.length_set]; exact hn, by
        rw [List.getElem_set_ne hnk]⟩

theorem Half.free_set_taken {h : Half} {k i : Nat} (hk : h.outs[k]? = some ⟨i, .offered⟩) (j : Nat) :
    Half.free { h with outs := h.outs.set k ⟨i, .taken⟩ } j = h.free j := by
  simp only [Half.free, Half.held_set_taken hk]

/-- An `own` and a `take` that can both be done on a half can be done in
    either order, to the same half. -/
theorem Half.diamond {h h₁ h₂ : Half} {o : OwnOp} {t : Option Nat}
    (ho : h.own o = some h₁) (ht : h.take t = some h₂) :
    ∃ h₁₂, h₁.take t = some h₁₂ ∧ h₂.own o = some h₁₂ := by
  cases t with
  | none =>
    simp only [Half.take] at ht ⊢
    cases ht
    exact ⟨h₁, rfl, ho⟩
  | some k =>
    simp only [Half.take] at ht
    split at ht
    · next i hk =>
      cases ht
      have hlt : k < h.outs.length := by
        rcases Nat.lt_or_ge k h.outs.length with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none hge] at hk; cases hk
      cases o with
      | free places grow =>
        simp only [Half.own] at ho ⊢
        split at ho
        · next hall =>
          cases ho
          have hall' : places.all (Half.free { h with outs := h.outs.set k ⟨i, .taken⟩ }) = true := by
            rw [List.all_eq_true] at hall ⊢
            intro j hj; rw [Half.free_set_taken hk]; exact hall j hj
          cases grow
          · exact ⟨{ h with outs := h.outs.set k ⟨i, .taken⟩ }, by simp [Half.take, hk],
              by simp [hall']⟩
          · exact ⟨{ n := h.n + 1, outs := h.outs.set k ⟨i, .taken⟩ }, by simp [Half.take, hk],
              by simp [hall']⟩
        · cases ho
      | out j k' =>
        simp only [Half.own] at ho ⊢
        split at ho
        · next hc =>
          cases ho
          refine ⟨{ h with outs := (h.outs.set k ⟨i, .taken⟩) ++ [⟨j, .offered⟩] }, ?_, ?_⟩
          · simp only [Half.take]
            rw [List.getElem?_append_left hlt, hk]
            simp only [List.set_append_left _ _ hlt]
          · rw [Half.free_set_taken hk, List.length_set]; simp [hc]
        · cases ho
      | ack k' j =>
        simp only [Half.own] at ho ⊢
        split at ho
        · next i' hk' =>
          split at ho
          · next hc =>
            cases ho
            have hne : k' ≠ k := by
              intro he; subst he; rw [hk] at hk'; cases hk'
            refine ⟨{ h with outs := (h.outs.set k ⟨i, .taken⟩).set k' ⟨i', .acked⟩ }, ?_, ?_⟩
            · simp only [Half.take]
              rw [List.getElem?_set_ne hne, hk]
              simp only [List.set_comm _ _ hne]
            · rw [List.getElem?_set_ne (Ne.symm hne), hk']
              simp [hc]
          · cases ho
        · cases ho
    · cases ht

/-! A shape: an entry of `a` and an entry of `b` commute. -/

theorem Side.other_ne (s : Side) : s.other ≠ s := by cases s <;> decide

theorem Shape.half_setHalf_same (sh : Shape) (s : Side) (h : Half) : (sh.setHalf s h).half s = h := by
  cases s <;> rfl

theorem Shape.half_setHalf_other (sh : Shape) {s u : Side} (h : Half) (hu : u ≠ s) :
    (sh.setHalf s h).half u = sh.half u := by
  cases s <;> cases u <;> first | rfl | exact absurd rfl hu

/-- What placing an entry is, half by half. -/
theorem Shape.place_eq {sh sh' : Shape} {s : Side} {e : Note} (h : sh.place s e = some sh') :
    (sh.half s).own e.own = some (sh'.half s) ∧
      (sh.half s.other).take e.taking = some (sh'.half s.other) := by
  unfold Shape.place at h
  split at h
  · next h₁ h₂ ho ht =>
    cases h
    refine ⟨?_, ?_⟩
    · rw [ho, Shape.half_setHalf_other _ _ (Side.other_ne s).symm, Shape.half_setHalf_same]
    · rw [ht, Shape.half_setHalf_same]
  · cases h

theorem Shape.ext_half {x y : Shape} (ha : x.half .a = y.half .a) (hb : x.half .b = y.half .b) :
    x = y := by
  cases x; cases y; simp only [Shape.half] at ha hb; subst ha; subst hb; rfl

theorem Shape.place_of {sh sh' : Shape} {s : Side} {e : Note}
    (ho : (sh.half s).own e.own = some (sh'.half s))
    (ht : (sh.half s.other).take e.taking = some (sh'.half s.other)) :
    sh.place s e = some sh' := by
  unfold Shape.place
  rw [ho, ht]
  simp only
  congr 1
  apply Shape.ext_half
  · cases s
    · simp [Shape.half, Shape.setHalf, Side.other]
    · simp [Shape.half, Shape.setHalf, Side.other]
  · cases s
    · simp [Shape.half, Shape.setHalf, Side.other]
    · simp [Shape.half, Shape.setHalf, Side.other]

/-- An entry of `a` and an entry of `b` that can both be placed can be placed
    in either order, to the same shape. -/
theorem Shape.diamond {sh s₁ s₂ : Shape} {x y : Note}
    (hx : sh.place .a x = some s₁) (hy : sh.place .b y = some s₂) :
    ∃ s₁₂, s₁.place .b y = some s₁₂ ∧ s₂.place .a x = some s₁₂ := by
  obtain ⟨hxo, hxt⟩ := Shape.place_eq hx
  obtain ⟨hyo, hyt⟩ := Shape.place_eq hy
  -- half `a`: `x`'s own and `y`'s take; half `b`: `y`'s own and `x`'s take.
  obtain ⟨ha, ha₁, ha₂⟩ := Half.diamond hxo hyt
  obtain ⟨hb, hb₁, hb₂⟩ := Half.diamond hyo hxt
  refine ⟨⟨ha, hb⟩, ?_, ?_⟩
  · exact Shape.place_of (sh' := ⟨ha, hb⟩) hb₂ ha₁
  · exact Shape.place_of (sh' := ⟨ha, hb⟩) ha₂ hb₁

/-- When some path exists and the head of `a` can be placed, a path exists
    after placing it. -/
theorem SPath.push {sh s₁ fin : Shape} {a b : List Note} (h : SPath sh a b fin) :
    ∀ {x : Note} {xs : List Note}, a = x :: xs → sh.place .a x = some s₁ → SPath s₁ xs b fin := by
  induction h generalizing s₁ with
  | done => intro x xs he; cases he
  | left hp rest _ =>
    intro x xs he hx
    cases he
    rw [hp] at hx; cases hx
    exact rest
  | right hp rest ih =>
    intro x xs he hx
    obtain ⟨s₁₂, h₁, h₂⟩ := Shape.diamond hx hp
    exact .right h₁ (ih he h₂)

/-! A `Mix` and its shape. -/

theorem Mix.places_setOuts (m : Mix) (s u : Side) (cs : List Crossing) :
    (m.setOuts s cs).places u = m.places u := by cases s <;> cases u <;> rfl

theorem Mix.places_grow_same (m : Mix) (s : Side) : (m.grow s).places s = m.places s ++ [m.total] := by
  cases s <;> rfl

theorem Mix.places_grow_other (m : Mix) {s u : Side} (h : u ≠ s) : (m.grow s).places u = m.places u := by
  cases s <;> cases u <;> first | rfl | exact absurd rfl h

theorem Mix.total_grow (m : Mix) (s : Side) : (m.grow s).total = m.total + 1 := by cases s <;> rfl

theorem Mix.total_setOuts (m : Mix) (s : Side) (cs : List Crossing) : (m.setOuts s cs).total = m.total := by
  cases s <;> rfl

theorem Mix.places_all (m : Mix) (g : Nat) :
    g ∈ m.placeA ++ m.placeB ↔ ∃ s, g ∈ m.places s := by
  rw [List.mem_append]
  constructor
  · rintro (h | h)
    · exact ⟨.a, h⟩
    · exact ⟨.b, h⟩
  · rintro ⟨s, h⟩
    cases s
    · exact .inl h
    · exact .inr h

theorem Mix.outs_all (m : Mix) (c : Crossing) : c ∈ m.outA ++ m.outB ↔ ∃ s, c ∈ m.outs s := by
  rw [List.mem_append]
  constructor
  · rintro (h | h)
    · exact ⟨.a, h⟩
    · exact ⟨.b, h⟩
  · rintro ⟨s, h⟩
    cases s
    · exact .inl h
    · exact .inr h

theorem nodup_index {l : List Nat} (h : l.Nodup) :
    ∀ {i j g : Nat}, l[i]? = some g → l[j]? = some g → i = j := by
  induction l with
  | nil => intro i j g hi; simp at hi
  | cons a l ih =>
    obtain ⟨hn, hl⟩ := List.nodup_cons.mp h
    intro i j g hi hj
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at hi hj
        cases hi
        exact absurd (List.mem_of_getElem? hj) hn
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at hi hj
        cases hj
        exact absurd (List.mem_of_getElem? hi) hn
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi hj
        rw [ih hl hi hj]

theorem lt_of_getElem? {α : Type} {l : List α} {k : Nat} {x : α} (h : l[k]? = some x) : k < l.length := by
  rcases Nat.lt_or_ge k l.length with hlt | hge
  · exact hlt
  · rw [List.getElem?_eq_none hge] at h; cases h

/-- A walk's state and a shape say the same: the global places are all
    different and below the count, each half has its guest's processes, and
    crossing by crossing the states agree and the asker's local place is at
    the asker's global place. -/
structure Shaped (m : Mix) (sh : Shape) : Prop where
  nodup : (m.placeA ++ m.placeB).Nodup
  below : ∀ g ∈ m.placeA ++ m.placeB, g < m.total
  n : ∀ s, (sh.half s).n = (m.places s).length
  len : ∀ s, (sh.half s).outs.length = (m.outs s).length
  outs : ∀ (s : Side) (k : Nat) (c : Crossing), (m.outs s)[k]? = some c →
    ∃ i, (sh.half s).outs[k]? = some ⟨i, c.state⟩ ∧ (m.places s)[i]? = some c.asker

theorem Shaped.first : Shaped Mix.first Shape.first where
  nodup := by simp [Mix.first]
  below := by simp [Mix.first]
  n := by intro s; cases s <;> rfl
  len := by intro s; cases s <;> rfl
  outs := by intro s k c h; cases s <;> simp [Mix.first, Mix.outs] at h

/-- One global place is one local place of one guest. -/
theorem Shaped.inj {m : Mix} {sh : Shape} (hs : Shaped m sh) {s u : Side} {i j g : Nat}
    (hi : (m.places s)[i]? = some g) (hj : (m.places u)[j]? = some g) : s = u ∧ i = j := by
  obtain ⟨ha, hb, hab⟩ := List.nodup_append.mp hs.nodup
  cases s <;> cases u
  · exact ⟨rfl, nodup_index ha hi hj⟩
  · exact absurd rfl (hab g (List.mem_of_getElem? hi) g (List.mem_of_getElem? hj))
  · exact absurd rfl (hab g (List.mem_of_getElem? hj) g (List.mem_of_getElem? hi))
  · exact ⟨rfl, nodup_index hb hi hj⟩

theorem Shaped.back_outs {m : Mix} {sh : Shape} (hs : Shaped m sh) {u : Side} {k i : Nat} {st : Crossed}
    (h : (sh.half u).outs[k]? = some ⟨i, st⟩) :
    ∃ g, (m.outs u)[k]? = some ⟨g, st⟩ ∧ (m.places u)[i]? = some g := by
  have hlt : k < (m.outs u).length := by rw [← hs.len u]; exact lt_of_getElem? h
  obtain ⟨i', h', hg⟩ := hs.outs u k _ (List.getElem?_eq_getElem hlt)
  rw [h] at h'
  cases h'
  exact ⟨(m.outs u)[k].asker, by rw [List.getElem?_eq_getElem hlt], hg⟩

theorem Mix.held_iff (m : Mix) (g : Nat) :
    m.held g = true ↔ ∃ (u : Side) (k : Nat) (c : Crossing), (m.outs u)[k]? = some c ∧ c.asker = g ∧ c.state ≠ .acked := by
  simp only [Mix.held, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hp⟩
    obtain ⟨u, hu⟩ := (m.outs_all c).mp hc
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hu
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    exact ⟨u, k, c, hk, hp.1, hp.2⟩
  · rintro ⟨u, k, c, hk, ha, hst⟩
    refine ⟨c, (m.outs_all c).mpr ⟨u, List.mem_of_getElem? hk⟩, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨ha, hst⟩

theorem Half.held_iff (h : Half) (i : Nat) :
    h.held i = true ↔ ∃ (k : Nat) (c : SCross), h.outs[k]? = some c ∧ c.asker = i ∧ c.state ≠ .acked := by
  simp only [Half.held, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hp⟩
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    exact ⟨k, c, hk, hp.1, hp.2⟩
  · rintro ⟨k, c, hk, ha, hst⟩
    refine ⟨c, List.mem_of_getElem? hk, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨ha, hst⟩

/-- A process is held in the walk's state exactly when it is in the shape. -/
theorem Shaped.held {m : Mix} {sh : Shape} (hs : Shaped m sh) {s : Side} {i g : Nat}
    (hi : (m.places s)[i]? = some g) : m.held g = (sh.half s).held i := by
  rw [Bool.eq_iff_iff, Mix.held_iff, Half.held_iff]
  constructor
  · rintro ⟨u, k, c, hk, ha, hst⟩
    obtain ⟨i', hk', hg⟩ := hs.outs u k c hk
    rw [ha] at hg
    obtain ⟨rfl, rfl⟩ := hs.inj hg hi
    exact ⟨k, _, hk', rfl, hst⟩
  · rintro ⟨k, ⟨i', st⟩, hk, ha, hst⟩
    cases ha
    obtain ⟨g', hk', hg⟩ := hs.back_outs hk
    rw [hi] at hg
    cases hg
    exact ⟨s, k, _, hk', rfl, hst⟩

theorem Shaped.free {m : Mix} {sh : Shape} (hs : Shaped m sh) {s : Side} {i g : Nat}
    (h : m.free s i = some g) : (m.places s)[i]? = some g ∧ (sh.half s).free i = true := by
  unfold Mix.free at h
  split at h
  · next g' hg =>
    split at h
    · cases h
    · next hh =>
      cases h
      refine ⟨hg, ?_⟩
      simp only [Half.free, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      refine ⟨by rw [hs.n s]; exact lt_of_getElem? hg, ?_⟩
      rw [← hs.held hg]
      simpa using hh
  · cases h

theorem Shaped.back_free {m : Mix} {sh : Shape} (hs : Shaped m sh) {s : Side} {i : Nat}
    (h : (sh.half s).free i = true) : ∃ g, m.free s i = some g ∧ (m.places s)[i]? = some g := by
  simp only [Half.free, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  have hlt : i < (m.places s).length := by rw [← hs.n s]; exact h.1
  have hg : (m.places s)[i]? = some (m.places s)[i] := List.getElem?_eq_getElem hlt
  refine ⟨(m.places s)[i], ?_, hg⟩
  unfold Mix.free
  rw [hg]
  simp only
  rw [hs.held hg, h.2]
  rfl

/-- One more process on guest `s`. -/
theorem Shaped.grow {m : Mix} {sh : Shape} (hs : Shaped m sh) (s : Side) :
    Shaped (m.grow s) (sh.setHalf s { sh.half s with n := (sh.half s).n + 1 }) where
  nodup := by
    have hfresh : ∀ g ∈ m.placeA ++ m.placeB, g ≠ m.total := fun g hg => Nat.ne_of_lt (hs.below g hg)
    obtain ⟨ha, hb, hab⟩ := List.nodup_append.mp hs.nodup
    cases s
    · show (m.placeA ++ [m.total] ++ m.placeB).Nodup
      rw [List.nodup_append]
      refine ⟨?_, hb, ?_⟩
      · rw [List.nodup_append]
        refine ⟨ha, by simp, ?_⟩
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst hy
        exact hfresh x (List.mem_append_left _ hx)
      · intro x hx y hy
        rcases List.mem_append.mp hx with hx | hx
        · exact hab x hx y hy
        · simp only [List.mem_singleton] at hx
          subst hx
          exact (hfresh y (List.mem_append_right _ hy)).symm
    · show (m.placeA ++ (m.placeB ++ [m.total])).Nodup
      rw [List.nodup_append]
      refine ⟨ha, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hb, by simp, ?_⟩
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst hy
        exact hfresh x (List.mem_append_right _ hx)
      · intro x hx y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hab x hx y hy
        · simp only [List.mem_singleton] at hy
          subst hy
          exact hfresh x (List.mem_append_left _ hx)
  below := by
    intro g hg
    rw [Mix.total_grow]
    have : g ∈ m.placeA ++ m.placeB ∨ g = m.total := by
      cases s
      · have hg' : g ∈ (m.placeA ++ [m.total]) ++ m.placeB := hg
        simp only [List.mem_append, List.mem_singleton] at hg' ⊢
        rcases hg' with (h | h) | h
        · exact .inl (.inl h)
        · exact .inr h
        · exact .inl (.inr h)
      · have hg' : g ∈ m.placeA ++ (m.placeB ++ [m.total]) := hg
        simp only [List.mem_append, List.mem_singleton] at hg' ⊢
        rcases hg' with h | h | h
        · exact .inl (.inl h)
        · exact .inl (.inr h)
        · exact .inr h
    rcases this with h | h
    · exact Nat.lt_succ_of_lt (hs.below g h)
    · rw [h]; exact Nat.lt_succ_self _
  n := by
    intro u
    by_cases hu : u = s
    · subst hu
      rw [Shape.half_setHalf_same, Mix.places_grow_same, List.length_append]
      simp [hs.n u]
    · rw [Shape.half_setHalf_other _ _ hu, Mix.places_grow_other _ hu]; exact hs.n u
  len := by
    intro u
    rw [Mix.outs_grow]
    by_cases hu : u = s
    · subst hu; rw [Shape.half_setHalf_same]; exact hs.len u
    · rw [Shape.half_setHalf_other _ _ hu]; exact hs.len u
  outs := by
    intro u k c hk
    rw [Mix.outs_grow] at hk
    obtain ⟨i, hi, hg⟩ := hs.outs u k c hk
    refine ⟨i, ?_, ?_⟩
    · by_cases hu : u = s
      · subst hu; rw [Shape.half_setHalf_same]; exact hi
      · rw [Shape.half_setHalf_other _ _ hu]; exact hi
    · by_cases hu : u = s
      · subst hu
        rw [Mix.places_grow_same, List.getElem?_append_left (lt_of_getElem? hg)]; exact hg
      · rw [Mix.places_grow_other _ hu]; exact hg

/-- Guest `s` changes its crossings; the places stay. -/
theorem Shaped.setOuts {m : Mix} {sh : Shape} (hs : Shaped m sh) (s : Side) {cs : List Crossing}
    {os : List SCross} (hlen : os.length = cs.length)
    (hall : ∀ (k : Nat) (c : Crossing), cs[k]? = some c → ∃ i, os[k]? = some ⟨i, c.state⟩ ∧ (m.places s)[i]? = some c.asker) :
    Shaped (m.setOuts s cs) (sh.setHalf s { sh.half s with outs := os }) where
  nodup := by cases s <;> exact hs.nodup
  below := by cases s <;> exact hs.below
  n := by
    intro u
    rw [Mix.places_setOuts]
    by_cases hu : u = s
    · subst hu; rw [Shape.half_setHalf_same]; exact hs.n u
    · rw [Shape.half_setHalf_other _ _ hu]; exact hs.n u
  len := by
    intro u
    by_cases hu : u = s
    · subst hu; rw [Shape.half_setHalf_same, Mix.outs_setOuts_same]; exact hlen
    · rw [Shape.half_setHalf_other _ _ hu, Mix.outs_setOuts_other _ _ hu]; exact hs.len u
  outs := by
    intro u k c hk
    by_cases hu : u = s
    · subst hu
      rw [Mix.outs_setOuts_same] at hk
      rw [Shape.half_setHalf_same, Mix.places_setOuts]
      exact hall k c hk
    · rw [Mix.outs_setOuts_other _ _ hu] at hk
      rw [Shape.half_setHalf_other _ _ hu, Mix.places_setOuts]
      exact hs.outs u k c hk

/-- A crossing of guest `u` moves on. -/
theorem Shaped.move {m : Mix} {sh : Shape} (hs : Shaped m sh) {u : Side} {k g : Nat} {st₀ : Crossed}
    (hk : (m.outs u)[k]? = some ⟨g, st₀⟩) (st : Crossed) :
    ∃ i, (sh.half u).outs[k]? = some ⟨i, st₀⟩ ∧ (m.places u)[i]? = some g ∧
      Shaped (m.setOuts u ((m.outs u).set k ⟨g, st⟩))
        (sh.setHalf u { sh.half u with outs := (sh.half u).outs.set k ⟨i, st⟩ }) := by
  obtain ⟨i, hi, hg⟩ := hs.outs u k _ hk
  refine ⟨i, hi, hg, hs.setOuts u (by rw [List.length_set, List.length_set]; exact hs.len u) ?_⟩
  intro n c hn
  by_cases hnk : k = n
  · subst hnk
    rw [List.getElem?_set_self (lt_of_getElem? hk)] at hn
    cases hn
    exact ⟨i, by rw [List.getElem?_set_self (lt_of_getElem? hi)], hg⟩
  · rw [List.getElem?_set_ne hnk] at hn
    obtain ⟨i', hi', hg'⟩ := hs.outs u n c hn
    exact ⟨i', by rw [List.getElem?_set_ne hnk]; exact hi', hg'⟩

/-- One more crossing of guest `s`, offered. -/
theorem Shaped.out {m : Mix} {sh : Shape} (hs : Shaped m sh) {s : Side} {i g : Nat}
    (hi : (m.places s)[i]? = some g) :
    Shaped (m.setOuts s (m.outs s ++ [⟨g, .offered⟩]))
      (sh.setHalf s { sh.half s with outs := (sh.half s).outs ++ [⟨i, .offered⟩] }) := by
  refine hs.setOuts s (by simp [hs.len s]) ?_
  intro k c hk
  rcases Nat.lt_or_ge k (m.outs s).length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hk
    obtain ⟨i', hi', hg'⟩ := hs.outs s k c hk
    exact ⟨i', by rw [List.getElem?_append_left (by rw [hs.len s]; exact hlt)]; exact hi', hg'⟩
  · rw [List.getElem?_append_right hge] at hk
    have hz : k - (m.outs s).length = 0 := by
      rcases Nat.eq_zero_or_pos (k - (m.outs s).length) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by simp only [List.length_singleton]; exact h)] at hk; cases hk
    rw [hz] at hk
    simp only [List.getElem?_cons_zero] at hk
    cases hk
    refine ⟨i, ?_, hi⟩
    rw [List.getElem?_append_right (by rw [hs.len s]; exact hge), hs.len s, hz]
    rfl

/-- What the walk's state places, its shape places, and they still say the
    same. -/
theorem Shaped.place {m m' : Mix} {sh : Shape} (hs : Shaped m sh) {s : Side} {e : Note}
    {evs : List Event} (hp : m.place s e = some (m', evs)) :
    ∃ sh', sh.place s e = some sh' ∧ Shaped m' sh' := by
  have hno : (Side.other s) ≠ s := Side.other_ne s
  cases e with
  | did ev =>
    cases ev with
    | fresh i n =>
      simp only [Mix.place] at hp
      cases hf : m.free s i with
      | none => simp [hf] at hp
      | some g =>
        simp [hf] at hp
        obtain ⟨rfl, _⟩ := hp
        exact ⟨sh, Shape.place_of (by simp [Note.own, Half.own, (hs.free hf).2])
          (by simp [Note.taking, Half.take]), hs⟩
    | spawn i =>
      simp only [Mix.place] at hp
      cases hf : m.free s i with
      | none => simp [hf] at hp
      | some g =>
        simp [hf] at hp
        obtain ⟨rfl, _⟩ := hp
        refine ⟨_, Shape.place_of ?_ ?_, hs.grow s⟩
        · rw [Shape.half_setHalf_same]; simp [Note.own, Half.own, (hs.free hf).2]
        · rw [Shape.half_setHalf_other _ _ hno]; simp [Note.taking, Half.take]
    | comm i j =>
      simp only [Mix.place] at hp
      split at hp
      · next g h hg hh =>
        cases hp
        exact ⟨sh, Shape.place_of (by simp [Note.own, Half.own, (hs.free hg).2, (hs.free hh).2])
          (by simp [Note.taking, Half.take]), hs⟩
      · cases hp
    | answer i x =>
      simp only [Mix.place] at hp
      cases hf : m.free s i with
      | none => simp [hf] at hp
      | some g =>
        simp [hf] at hp
        obtain ⟨rfl, _⟩ := hp
        exact ⟨sh, Shape.place_of (by simp [Note.own, Half.own, (hs.free hf).2])
          (by simp [Note.taking, Half.take]), hs⟩
  | out i k =>
    simp only [Mix.place] at hp
    split at hp
    · next g hg =>
      split at hp
      · next hk =>
        cases hp
        obtain ⟨hpl, hfr⟩ := hs.free hg
        refine ⟨_, Shape.place_of ?_ ?_, hs.out hpl⟩
        · rw [Shape.half_setHalf_same]; simp [Note.own, Half.own, hfr, hk, hs.len s]
        · rw [Shape.half_setHalf_other _ _ hno]; simp [Note.taking, Half.take]
      · cases hp
    · cases hp
  | spawnIn k =>
    simp only [Mix.place] at hp
    split at hp
    · next g hg =>
      cases hp
      obtain ⟨i, hi, _, hsim⟩ := hs.move hg .taken
      refine ⟨_, Shape.place_of ?_ ?_, hsim.grow s⟩
      · rw [Shape.half_setHalf_same, Shape.half_setHalf_other _ _ hno.symm]
        simp [Note.own, Half.own]
      · rw [Shape.half_setHalf_other _ _ hno, Shape.half_setHalf_same]
        simp [Note.taking, Half.take, hi]
    · cases hp
  | sendIn k j =>
    simp only [Mix.place] at hp
    split at hp
    · next g h hg hf =>
      cases hp
      obtain ⟨i, hi, _, hsim⟩ := hs.move hg .taken
      refine ⟨_, Shape.place_of ?_ ?_, hsim⟩
      · rw [Shape.half_setHalf_other _ _ hno.symm]
        simp [Note.own, Half.own, (hs.free hf).2]
      · rw [Shape.half_setHalf_same]
        simp [Note.taking, Half.take, hi]
    · cases hp
  | ack k i =>
    simp only [Mix.place] at hp
    split at hp
    · next g g' hg hg' =>
      split at hp
      · next heq =>
        cases hp
        subst heq
        obtain ⟨i', hi', hpl, hsim⟩ := hs.move hg .acked
        obtain ⟨_, rfl⟩ := hs.inj hpl hg'
        refine ⟨_, Shape.place_of ?_ ?_, hsim⟩
        · rw [Shape.half_setHalf_same]
          have hlt : i' < (sh.half s).n := by rw [hs.n s]; exact lt_of_getElem? hg'
          simp [Note.own, Half.own, hi', hlt]
        · rw [Shape.half_setHalf_other _ _ hno]; simp [Note.taking, Half.take]
      · cases hp
    · cases hp
  | held _ =>
    simp only [Mix.place] at hp
    cases hp
    exact ⟨sh, Shape.place_of (by simp [Note.own, Half.own]) (by simp [Note.taking, Half.take]), hs⟩
  | full _ =>
    simp only [Mix.place] at hp
    cases hp
    exact ⟨sh, Shape.place_of (by simp [Note.own, Half.own]) (by simp [Note.taking, Half.take]), hs⟩

/-- What the shape places, the walk's state places. -/
theorem Shaped.back_some {m : Mix} {sh sh' : Shape} (hs : Shaped m sh) {s : Side} {e : Note}
    (hp : sh.place s e = some sh') : (m.place s e).isSome = true := by
  obtain ⟨ho, ht⟩ := Shape.place_eq hp
  cases e with
  | did ev =>
    cases ev with
    | fresh i n =>
      simp only [Note.own, Half.own] at ho
      split at ho
      · next hall =>
        simp only [List.all_cons, List.all_nil, Bool.and_true] at hall
        obtain ⟨g, hf, _⟩ := hs.back_free hall
        simp [Mix.place, hf]
      · cases ho
    | spawn i =>
      simp only [Note.own, Half.own] at ho
      split at ho
      · next hall =>
        simp only [List.all_cons, List.all_nil, Bool.and_true] at hall
        obtain ⟨g, hf, _⟩ := hs.back_free hall
        simp [Mix.place, hf]
      · cases ho
    | comm i j =>
      simp only [Note.own, Half.own] at ho
      split at ho
      · next hall =>
        simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hall
        obtain ⟨g, hf, _⟩ := hs.back_free hall.1
        obtain ⟨g', hf', _⟩ := hs.back_free hall.2
        simp [Mix.place, hf, hf']
      · cases ho
    | answer i x =>
      simp only [Note.own, Half.own] at ho
      split at ho
      · next hall =>
        simp only [List.all_cons, List.all_nil, Bool.and_true] at hall
        obtain ⟨g, hf, _⟩ := hs.back_free hall
        simp [Mix.place, hf]
      · cases ho
  | out i k =>
    simp only [Note.own, Half.own] at ho
    split at ho
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨g, hf, _⟩ := hs.back_free hc.1
      have hk : k = (m.outs s).length := by rw [← hs.len s]; exact hc.2
      simp [Mix.place, hf, hk]
    · cases ho
  | spawnIn k =>
    simp only [Note.taking, Half.take] at ht
    split at ht
    · next i hi =>
      obtain ⟨g, hg, _⟩ := hs.back_outs hi
      simp [Mix.place, hg]
    · cases ht
  | sendIn k j =>
    simp only [Note.taking, Half.take] at ht
    simp only [Note.own, Half.own] at ho
    split at ht
    · next i hi =>
      split at ho
      · next hall =>
        simp only [List.all_cons, List.all_nil, Bool.and_true] at hall
        obtain ⟨g, hg, _⟩ := hs.back_outs hi
        obtain ⟨h, hf, _⟩ := hs.back_free hall
        simp [Mix.place, hg, hf]
      · cases ho
    · cases ht
  | ack k i =>
    simp only [Note.own, Half.own] at ho
    split at ho
    · next i' hi =>
      split at ho
      · next hc =>
        obtain ⟨rfl, _⟩ := hc
        obtain ⟨g, hg, hpl⟩ := hs.back_outs hi
        simp [Mix.place, hg, hpl]
      · cases ho
    · cases ho
  | held _ => simp [Mix.place]
  | full _ => simp [Mix.place]

theorem Shaped.back {m : Mix} {sh sh' : Shape} (hs : Shaped m sh) {s : Side} {e : Note}
    (hp : sh.place s e = some sh') : ∃ m' evs, m.place s e = some (m', evs) := by
  have h := hs.back_some hp
  cases hm : m.place s e with
  | none => rw [hm] at h; cases h
  | some r => exact ⟨r.1, r.2, rfl⟩

theorem Shape.outs_all (sh : Shape) (c : SCross) :
    c ∈ sh.a.outs ++ sh.b.outs ↔ ∃ s, c ∈ (sh.half s).outs := by
  rw [List.mem_append]
  constructor
  · rintro (h | h)
    · exact ⟨.a, h⟩
    · exact ⟨.b, h⟩
  · rintro ⟨s, h⟩
    cases s
    · exact .inl h
    · exact .inr h

/-- The walk's state is settled exactly when its shape is. -/
theorem Shaped.settled {m : Mix} {sh : Shape} (hs : Shaped m sh) : m.settled = sh.settled := by
  rw [Bool.eq_iff_iff]
  simp only [Mix.settled, Shape.settled, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h sc hsc
    obtain ⟨u, hu⟩ := (sh.outs_all sc).mp hsc
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hu
    obtain ⟨g, hg, _⟩ := hs.back_outs (i := sc.asker) (st := sc.state) hk
    exact h _ ((m.outs_all _).mpr ⟨u, List.mem_of_getElem? hg⟩)
  · intro h c hc
    obtain ⟨u, hu⟩ := (m.outs_all c).mp hc
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hu
    obtain ⟨i, hi, _⟩ := hs.outs u k c hk
    exact h _ ((sh.outs_all _).mpr ⟨u, List.mem_of_getElem? hi⟩)

/-- A walk the table allows is a path on shapes, to a settled shape. -/
theorem Walk.spath {m last : Mix} {a b : List Note} {tr : List (Side × Note)} {evs : List Event}
    (h : Walk m a b tr evs last) :
    ∀ {sh : Shape}, Shaped m sh → ∃ fin, SPath sh a b fin ∧ Shaped last fin ∧ fin.settled = true := by
  induction h with
  | done hset => intro sh hs; exact ⟨sh, .done, hs, by rw [← hs.settled]; exact hset⟩
  | left hp _ ih =>
    intro sh hs
    obtain ⟨sh', hpl, hs'⟩ := hs.place hp
    obtain ⟨fin, hpath, hf, hset⟩ := ih hs'
    exact ⟨fin, .left hpl hpath, hf, hset⟩
  | right hp _ ih =>
    intro sh hs
    obtain ⟨sh', hpl, hs'⟩ := hs.place hp
    obtain ⟨fin, hpath, hf, hset⟩ := ih hs'
    exact ⟨fin, .right hpl hpath, hf, hset⟩

/-- The greedy walk finds its way wherever a path to a settled shape exists. -/
theorem mix_complete : ∀ (fuel : Nat) (m : Mix) (sh fin : Shape) (a b : List Note),
    Shaped m sh → SPath sh a b fin → fin.settled = true → a.length + b.length ≤ fuel →
    ∃ r, mix fuel m a b = some r := by
  intro fuel
  induction fuel with
  | zero =>
    intro m sh fin a b hs hp hset hlen
    cases a with
    | nil =>
      cases b with
      | nil =>
        cases hp
        exact ⟨([], m), by simp [mix, hs.settled, hset]⟩
      | cons y ys => simp at hlen
    | cons x xs => simp at hlen
  | succ fuel ih =>
    intro m sh fin a b hs hp hset hlen
    cases a with
    | nil =>
      cases b with
      | nil =>
        cases hp
        exact ⟨([], m), by simp [mix, hs.settled, hset]⟩
      | cons y ys =>
        cases hp with
        | right h rest =>
          obtain ⟨m₂, evs, hm⟩ := hs.back h
          obtain ⟨sh₂, hpl, hs₂⟩ := hs.place hm
          rw [h] at hpl
          cases hpl
          obtain ⟨r, hr⟩ := ih m₂ _ fin [] ys hs₂ rest hset (by simp at hlen ⊢; omega)
          exact ⟨((Side.b, y, evs) :: r.1, r.2), by simp [mix, hm, hr]⟩
    | cons x xs =>
      cases hm : m.place .a x with
      | some r =>
        obtain ⟨m', evs⟩ := r
        obtain ⟨sh', hpl, hs'⟩ := hs.place hm
        obtain ⟨r, hr⟩ := ih m' sh' fin xs b hs' (hp.push rfl hpl) hset (by simp at hlen ⊢; omega)
        exact ⟨((Side.a, x, evs) :: r.1, r.2), by simp [mix, hm, hr]⟩
      | none =>
        cases hp with
        | left h rest =>
          obtain ⟨m', evs, hm'⟩ := hs.back h
          rw [hm] at hm'; cases hm'
        | @right _ _ y _ ys _ h rest =>
          obtain ⟨m₂, evs, hm₂⟩ := hs.back h
          obtain ⟨sh₂, hpl, hs₂⟩ := hs.place hm₂
          rw [h] at hpl
          cases hpl
          obtain ⟨r, hr⟩ := ih m₂ _ fin (x :: xs) ys hs₂ rest hset (by simp at hlen ⊢; omega)
          exact ⟨((Side.b, y, evs) :: r.1, r.2), by simp [mix, hm, hm₂, hr]⟩

/-- Two logs with a path on shapes from the first shape to a settled one
    combine. -/
theorem spath_combine {a b : List Note} {fin : Shape} (h : SPath Shape.first a b fin)
    (hset : fin.settled = true) : ∃ t last, combineTrace a b = some (t, last) := by
  obtain ⟨⟨t, last⟩, hr⟩ := mix_complete _ _ _ _ a b Shaped.first h hset (Nat.le_refl _)
  exact ⟨t, last, hr⟩

/-- The greedy walk is complete: two logs that have any schedule the table
    allows combine. -/
theorem combine_complete {a b : List Note} {evs : List Event} (h : Merged a b evs) :
    ∃ evs', combine a b = some evs' := by
  obtain ⟨tr, last, hw⟩ := h
  obtain ⟨fin, hpath, _, hset⟩ := hw.spath Shaped.first
  obtain ⟨t, last', hr⟩ := spath_combine hpath hset
  exact ⟨traceEvents t, by simp [combine, combineMix, hr]⟩

end Reflect
