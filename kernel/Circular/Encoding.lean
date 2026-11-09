import Circular.Semantics

namespace Circular

/-- Church indices, including the two binders in every successor. -/
def church : Nat → Term
  | 0 => .lam (.lam (.var 0))
  | n + 1 => .lam (.lam (.app (.var 1)
      (.app (.app (shift 2 0 (church n)) (.var 1)) (.var 0))))

theorem church_pure (n : Nat) : Pure (church n) := by
  induction n with
  | zero => exact .lam (.lam (.var 0))
  | succ n ih => exact .lam (.lam (.app (.var 1)
      (.app (.app (shift_pure ih) (.var 1)) (.var 0))))

theorem church_closed (n : Nat) : Closed (church n) := by
  induction n with
  | zero => decide
  | succ n ih =>
    exact ⟨by decide, ⟨⟨by simpa using shift_scoped (k := 2) (c := 0) ih, by decide⟩, by decide⟩⟩

/-- The proof argument excludes quote; there is no encoding of quoted code. -/
def encode (p : Term) (h : Pure p) : Term :=
  match p with
  | .var i => .lam (.lam (.lam (.app (.var 2) (shift 3 0 (church i)))))
  | .lam b => .lam (.lam (.lam (.app (.var 1)
      (shift 3 0 (encode b (pure_lam.mp h))))))
  | .app f a => .lam (.lam (.lam (.app
      (.app (.var 0) (shift 3 0 (encode f (pure_app.mp h).1)))
      (shift 3 0 (encode a (pure_app.mp h).2)))))
  | .quote _ => False.elim (not_pure_quote h)

theorem encode_pure (h : Pure p) : Pure (encode p h) := by
  induction p with
  | var i => exact .lam (.lam (.lam (.app (.var 2) (shift_pure (church_pure i)))))
  | lam b ih => exact .lam (.lam (.lam (.app (.var 1) (shift_pure (ih _)))))
  | app f a ihf iha => exact .lam (.lam (.lam (.app
      (.app (.var 0) (shift_pure (ihf _))) (shift_pure (iha _)))))
  | quote => exact False.elim (not_pure_quote h)

theorem encode_closed (h : Pure p) : Closed (encode p h) := by
  induction p with
  | var i => exact ⟨by decide, by simpa using shift_scoped (k := 3) (c := 0) (church_closed i)⟩
  | lam b ih => exact ⟨by decide, by simpa using shift_scoped (k := 3) (c := 0) (ih _)⟩
  | app f a ihf iha => exact ⟨⟨by decide, by simpa using shift_scoped (k := 3) (c := 0) (ihf _)⟩, by simpa using shift_scoped (k := 3) (c := 0) (iha _)⟩
  | quote => exact False.elim (not_pure_quote h)

end Circular
