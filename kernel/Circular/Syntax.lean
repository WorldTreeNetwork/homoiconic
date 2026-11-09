import Std

namespace Circular

/-- De Bruijn index zero denotes the nearest binder. Quote is syntax. -/
inductive Term where
  | var : Nat → Term
  | lam : Term → Term
  | app : Term → Term → Term
  | quote : Term → Term
  deriving DecidableEq, Repr

/-- All and only quote-free terms, whether open, closed, or diverging. -/
inductive Pure : Term → Prop where
  | var (i) : Pure (.var i)
  | lam : Pure b → Pure (.lam b)
  | app : Pure f → Pure a → Pure (.app f a)

@[simp] theorem pure_var : Pure (.var i) := .var i
@[simp] theorem pure_lam : Pure (.lam b) ↔ Pure b :=
  ⟨fun h => by cases h; assumption, .lam⟩
@[simp] theorem pure_app : Pure (.app f a) ↔ Pure f ∧ Pure a :=
  ⟨fun h => by cases h; exact ⟨‹_›, ‹_›⟩, fun ⟨hf, ha⟩ => .app hf ha⟩
@[simp] theorem not_pure_quote : ¬ Pure (.quote t) := fun h => by cases h

/-- A bound on every free index; this does not restrict `Pure`. -/
def Scoped : Nat → Term → Prop
  | n, .var i => i < n
  | n, .lam b => Scoped (n + 1) b
  | n, .app f a => Scoped n f ∧ Scoped n a
  | _, .quote _ => True

instance scopedDecidable (n : Nat) (t : Term) : Decidable (Scoped n t) :=
  match t with
  | .var i => inferInstanceAs (Decidable (i < n))
  | .lam b => scopedDecidable (n + 1) b
  | .app f a => @instDecidableAnd _ _ (scopedDecidable n f) (scopedDecidable n a)
  | .quote _ => isTrue trivial

abbrev Closed (t : Term) := Scoped 0 t

/-- Shift free variables when embedding syntax beneath additional binders. -/
def shift (amount cutoff : Nat) : Term → Term
  | .var i => .var (if i < cutoff then i else i + amount)
  | .lam b => .lam (shift amount (cutoff + 1) b)
  | .app f a => .app (shift amount cutoff f) (shift amount cutoff a)
  | .quote t => .quote t

theorem shift_pure (h : Pure t) : Pure (shift k c t) := by
  induction h generalizing c with
  | var => exact .var _
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha

theorem shift_scoped (h : Scoped n t) : Scoped (n + k) (shift k c t) := by
  induction t generalizing n c with
  | var i =>
    simp only [Scoped, shift] at *
    split <;> omega
  | lam b ih =>
    simpa [Scoped, shift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (n := n + 1) (c := c + 1) h
  | app f a ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | quote => trivial

theorem shift_eq_self_of_scoped (h : Scoped c t) : shift k c t = t := by
  induction t generalizing c with
  | var i =>
    change i < c at h
    simp [shift, h]
  | lam b ih => simp [shift, ih h]
  | app f a ihf iha => simp [shift, ihf h.1, iha h.2]
  | quote => rfl

end Circular
