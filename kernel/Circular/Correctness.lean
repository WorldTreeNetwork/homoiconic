import Circular.InterpreterProof

namespace Circular

/-- Direct evaluation and object-language interpretation agree for every
    quote-free program, including open programs and unbound outcomes. -/
theorem metacircular : ∀ p (h : Pure p), ∀ o,
    Direct [] p o ↔
    ∃ w, Direct [] (.app interpreterBody (encode p h)) w ∧ Represents o w := by
  intro p hp o
  constructor
  · exact interpreter_complete hp
  · rintro ⟨w, hw, hr⟩
    obtain ⟨o', hd, hr'⟩ := interpreter_sound hp hw
    cases Represents_unique hr hr'
    exact hd

/-- Coverage is quantified over every interpreter derivation, so the
    correspondence also preserves absence of a source derivation. -/
theorem coverage : ∀ p (h : Pure p), ∀ w,
    Direct [] (.app interpreterBody (encode p h)) w →
    ∃ o, Represents o w := by
  intro p hp w hw
  obtain ⟨o, _, hr⟩ := interpreter_sound hp hw
  exact ⟨o, hr⟩

end Circular
