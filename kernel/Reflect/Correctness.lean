import Reflect.Proof

namespace Reflect
variable [Ops]

/-- Direct evaluation and interpretation agree for every program. The program
    is passed as its own data form and the answer is compared by equality. -/
theorem reflective : ∀ p o,
    Direct [] p o ↔
    Direct [] (.app interp (.lit (reify p))) (.value (.data (reifyOutcome o))) := by
  intro p o
  rw [interp_iff]
  exact core_iff _ [] p o

/-- Every answer of the interpreter is the data form of a source outcome. -/
theorem reflective_coverage : ∀ p w,
    Direct [] (.app interp (.lit (reify p))) w →
    ∃ o, w = .value (.data (reifyOutcome o)) := by
  intro p w h
  obtain ⟨o, ho, _⟩ := core_sound (env := []) _ ((interp_iff _ _).mp h)
  exact ⟨o, ho⟩

/-- The same statement at every environment, with the environment as data. -/
theorem reflective_env : ∀ env p o,
    Direct env p o ↔
    Direct [] (.app (.app evalTerm (.lit (reify p))) (.lit (.arr (reifyEnv env))))
      (.value (.data (reifyOutcome o))) := by
  intro env p o
  have h : evalTerm = .app fixT (.lam (.lam (.lam core))) := rfl
  rw [h, eval_iff .lit .lit]
  exact core_iff _ env p o

/-- The interpreter interprets itself to any depth. -/
theorem tower : ∀ k p o, Direct [] p o ↔ Direct [] (level k p) (lift k o) := by
  intro k
  induction k with
  | zero => intro p o; exact Iff.rfl
  | succ k ih =>
    intro p o
    exact (ih p o).trans (reflective (level k p) (lift k o))

end Reflect
