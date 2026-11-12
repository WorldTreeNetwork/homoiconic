import Reflect

open Reflect

-- Acceptance check for `add-state-store`. It fails to compile until the
-- theorems exist with exactly these signatures, for every table of operations
-- and every kind of reference `R`. This file does not import a table.

-- Saving loses nothing. A state held whole resolves to itself under any store,
-- a piece put under a reference can be replaced by the reference, and a state
-- that resolves still resolves when the store holds more.
example : ∀ {R : Type} (σ : Store R) (s : State), RState σ s.toP s := Reflect.saved_resolves

example : ∀ {R : Type} {σ : Store R} {r : R} {p q : P R},
    σ r = some p → Unf σ p q → Unf σ (.ref r) q := Reflect.cut_resolves

example : ∀ {R : Type} {σ τ : Store R}, σ.le τ → ∀ {ps : PState R} {s : State},
    RState σ ps s → RState τ ps s := Reflect.RState.mono

-- A piece resolves to one thing, and a partial outcome to one outcome.
example : ∀ {R : Type} {σ : Store R} {p q q' : P R}, Unf σ p q → Unf σ p q' → q = q' :=
  Reflect.Unf.unique

example : ∀ {R : Type} {σ : Store R} {po : POutcome R} {o o' : MOutcome},
    ROutcome σ po o → ROutcome σ po o' → o = o' := Reflect.resolve_unique

-- Hydration is invisible. For every number of plain steps the lazy machine
-- reaches a state that resolves to the plain machine's state.
example : ∀ [Ops] {R : Type} {σ : Store R} (n : Nat) {ps : PState R} {s : State},
    RState σ ps s → ∃ k ps', n ≤ k ∧ lrun σ k ps = .at ps' ∧ RState σ ps' (run n s) :=
  Reflect.lazy_simulates

example : ∀ [Ops] {R : Type} {σ : Store R} {ps : PState R} {s : State}, RState σ ps s →
    ∀ {n : Nat} {o : MOutcome}, run n s = .halted o →
    ∃ k po, lrun σ k ps = .at (.halted po) ∧ ROutcome σ po o :=
  Reflect.lazy_complete

-- A missing piece is a pause. Under any part of the store, what the lazy
-- machine halts with is what the plain machine halts with.
example : ∀ [Ops] {R : Type} {σ σ' : Store R}, σ'.le σ → ∀ {ps : PState R} {s : State},
    RState σ ps s → ∀ {k : Nat} {po : POutcome R}, lrun σ' k ps = .at (.halted po) →
    ∃ o, run k s = .halted o ∧ ROutcome σ po o :=
  Reflect.lazy_sound

-- A run pauses only on a reference the store lacks. Under any store that
-- holds more, the run from the start passes through the paused state.
example : ∀ [Ops] {R : Type} {σ' τ : Store R}, σ'.le τ →
    ∀ {k : Nat} {ps ps' : PState R} {r : R}, lrun σ' k ps = .paused r ps' →
    σ' r = none ∧ ∃ j, j < k ∧ ∀ n, lrun τ (j + n) ps = lrun τ n ps' :=
  Reflect.lazy_pause

-- More pieces change nothing.
example : ∀ [Ops] {R : Type} {σ τ : Store R}, σ.le τ → ∀ (k : Nat) {ps ps' : PState R},
    lrun σ k ps = .at ps' → lrun τ k ps = .at ps' :=
  Reflect.lrun_mono

-- Any substrate will do: stores that agree wherever both hold a piece give
-- the same result.
example : ∀ [Ops] {R : Type} {σ₁ σ₂ : Store R}, σ₁.Compatible σ₂ →
    ∀ {ps : PState R} {k₁ k₂ : Nat} {po₁ po₂ : POutcome R},
    lrun σ₁ k₁ ps = .at (.halted po₁) → lrun σ₂ k₂ ps = .at (.halted po₂) → po₁ = po₂ :=
  Reflect.lazy_agree

-- A program run through the store has the outcome direct evaluation gives it.
example : ∀ [Ops] {R : Type} (σ : Store R) (t : Term) (o : Outcome),
    Direct [] t o ↔
    ∃ k po w, lrun σ k (.running (compile t) .nil [] []) = .at (.halted po) ∧
      ROutcome σ po w ∧ readOutcome w = some o :=
  Reflect.lazy_program

-- A waiting run kept in the store: a turn of the request driver from the
-- stored continuation is a turn of the machine.
example : ∀ [Ops] {R : Type} {σ : Store R} {pc : P R} {c : MValue}, RValue σ pc c →
    ∀ {t : Term} {w : MOutcome}, machine.eval c t w →
    ∃ k po, lrun σ k (.running (compile t) (.cons pc .nil) [] []) = .at (.halted po) ∧
      ROutcome σ po w :=
  Reflect.lazy_turn_complete

example : ∀ [Ops] {R : Type} {σ σ' : Store R}, σ'.le σ → ∀ {pc : P R} {c : MValue},
    RValue σ pc c → ∀ {t : Term} {k : Nat} {po : POutcome R},
    lrun σ' k (.running (compile t) (.cons pc .nil) [] []) = .at (.halted po) →
    ∃ w, machine.eval c t w ∧ ROutcome σ po w :=
  Reflect.lazy_turn_sound

#print axioms Reflect.saved_resolves
#print axioms Reflect.cut_resolves
#print axioms Reflect.RState.mono
#print axioms Reflect.Unf.unique
#print axioms Reflect.resolve_unique
#print axioms Reflect.lazy_simulates
#print axioms Reflect.lazy_complete
#print axioms Reflect.lazy_sound
#print axioms Reflect.lazy_pause
#print axioms Reflect.lrun_mono
#print axioms Reflect.lazy_agree
#print axioms Reflect.lazy_program
#print axioms Reflect.lazy_turn_complete
#print axioms Reflect.lazy_turn_sound
