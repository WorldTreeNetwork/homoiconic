import Surface.CrossModel

/-!
The two guests `kernel/CrossCheck.lean` runs in one process are guests of the
model.

`Surface.Cross.simulateWith` makes its pair with `Guest.work`, `Guest.batch`
and `Guest.take`, which speak of bytes. `Reach.simulate`: when a batch's bytes
read back as the batch (`ReadsBack`, tested as P4 and not proved, so it is a
hypothesis here), that pair is one the model reaches.
So the theorems of `Surface.CrossProof` are about the pairs the check runs.
The image's exchanges are Zig and are not spoken of here.
-/
namespace Surface.Cross
open Reflect

theorem Guest.work_zero (cnt : Guest → Nat) (g : Guest) : g.work cnt 0 = g := rfl

theorem Guest.work_step (cnt : Guest → Nat) {g g' : Guest} (n : Nat) (h : g.step cnt = some g') :
    g.work cnt (n + 1) = g'.work cnt n := by
  simp [Guest.work, h]

theorem Guest.work_rest (cnt : Guest → Nat) {g : Guest} (n : Nat) (h : g.step cnt = none) :
    g.work cnt (n + 1) = { g with resting := true } := by
  simp [Guest.work, h]

/-- `Guest.work` is steps of the model and, when no step is possible, its
    rest. -/
theorem Reach.workA (cnt : Guest → Nat) (n : Nat) : ∀ {s : Pair}, Reach s →
    Reach { s with a := s.a.work cnt n } := by
  induction n with
  | zero => intro s h; exact h
  | succ n ih =>
    intro s h
    cases hs : s.a.step cnt with
    | none => rw [Guest.work_rest cnt n hs]; exact .move h (.restA cnt hs)
    | some g => rw [Guest.work_step cnt n hs]; exact ih (.move h (.stepA cnt hs))

theorem Reach.workB (cnt : Guest → Nat) (n : Nat) : ∀ {s : Pair}, Reach s →
    Reach { s with b := s.b.work cnt n } := by
  induction n with
  | zero => intro s h; exact h
  | succ n ih =>
    intro s h
    cases hs : s.b.step cnt with
    | none => rw [Guest.work_rest cnt n hs]; exact .move h (.restB cnt hs)
    | some g => rw [Guest.work_step cnt n hs]; exact ih (.move h (.stepB cnt hs))

/-- A batch's bytes read back as the batch. Tested (P4), not proved, and not
    provable here: the writer is a `partial` definition, so the logic sees it
    as opaque. It is asked of every guest value, which is more than the
    batches of one run. -/
def ReadsBack : Prop :=
  ∀ (g : Guest) (room : Nat), Wire.read (Wire.write (g.batchData room)) = .ok (g.batchData room)

/-- Taking the bytes of a batch is taking the batch, when bytes read back. -/
theorem Guest.take_batch (hread : ReadsBack) (g h : Guest)
    (room : Nat) : g.take (h.batch room) = g.takeData (h.batchData room) := by
  rw [Guest.take_eq, Guest.batch_eq, hread h room]

/-- One exchange of the pair in one process: the caller, `b`, works and sends;
    `a` takes, works and answers; `b` takes the answer. -/
theorem Reach.exchange (hread : ReadsBack) (cb ca : Guest → Nat)
    {s : Pair} (h : Reach s) :
    ∃ s', Reach s' ∧ (s'.b, s'.a) = exchange cb ca (s.b, s.a) ∧ s'.prog = s.prog := by
  have h₁ := Reach.workB cb workLimit h
  have h₂ : Reach _ := .move h₁ (.sendB roomLimit)
  have h₃ : Reach _ := .move h₂ (.takeA (d := (s.b.work cb workLimit).batchData roomLimit)
    List.mem_cons_self)
  have h₄ := Reach.workA ca workLimit h₃
  have h₅ : Reach _ := .move h₄ (.sendA roomLimit)
  have h₆ : Reach _ := .move h₅ (.takeB
    (d := ((s.a.takeData ((s.b.work cb workLimit).batchData roomLimit)).work ca workLimit).batchData
      roomLimit) List.mem_cons_self)
  refine ⟨_, h₆, ?_, rfl⟩
  simp [Surface.Cross.exchange, Guest.take_batch hread]

/-- As many exchanges as `pump` makes. -/
theorem Reach.pump (hread : ReadsBack) (cb ca : Guest → Nat)
    (n : Nat) : ∀ {s : Pair}, Reach s →
    ∃ s', Reach s' ∧ (s'.b, s'.a) = pump cb ca n (s.b, s.a) ∧ s'.prog = s.prog := by
  induction n with
  | zero => intro s h; exact ⟨s, h, rfl, rfl⟩
  | succ n ih =>
    intro s h
    by_cases hc : s.b.closed = true
    · exact ⟨s, h, by simp [Surface.Cross.pump, hc], rfl⟩
    · obtain ⟨s₁, h₁, he₁, hp₁⟩ := Reach.exchange hread cb ca h
      obtain ⟨s₂, h₂, he₂, hp₂⟩ := ih h₁
      refine ⟨s₂, h₂, ?_, hp₂.trans hp₁⟩
      rw [he₂, he₁]
      simp [Surface.Cross.pump, hc]

/-- The pair `simulateWith` makes is one the model reaches: the caller is the
    model's `b`, the guest given the program its `a`, and the program the
    model keeps is the one the bytes read as. -/
theorem Reach.simulate (hread : ReadsBack) (program : ByteArray) (u : Setup) :
    ∃ s, Reach s ∧ (s.b, s.a) = simulateWith program u ∧
      s.prog = (Wire.readProgram program).toOption := by
  have h₀ : Reach _ := .move
    (.first ⟨false, u.far, u.takeNew, u.limitA, u.turnA, u.holdA⟩
      ⟨true, false, false, u.limitB, u.turnB, u.holdB⟩) (.giveA program u.frame)
  obtain ⟨s, h, he, hp⟩ := Reach.pump hread u.countB u.countA u.exchanges h₀
  refine ⟨s, h, he, hp.trans ?_⟩
  show handed (start true false u.far u.takeNew u.limitA u.turnA u.holdA) program none = _
  cases hr : Wire.readProgram program <;> simp [handed, start, hr, Except.toOption]

end Surface.Cross
