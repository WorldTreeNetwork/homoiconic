namespace Reflect

/-- First-order data. This is the abstract type; a wire format is elsewhere. -/
inductive Data where
  | nat : Nat → Data
  | arr : List Data → Data
  /-- A channel name. `succ`, `case` and the operation number of `prim` see it
      as its number; nothing in the language makes one. -/
  | name : Nat → Data
  deriving Repr, BEq

/-- De Bruijn index zero is the nearest binder. `lit d` denotes `d` and is
    never looked inside by evaluation. Quoting a program is `lit (reify p)`. -/
inductive Term where
  | var : Nat → Term
  | lam : Term → Term
  | app : Term → Term → Term
  | lit : Data → Term
  | succ : Term → Term
  | cons : Term → Term → Term
  /-- Scrutinee; zero branch; successor branch (binds the predecessor);
      empty branch; non-empty branch (binds the head at 1 and the tail at 0). -/
  | dcase : Term → Term → Term → Term → Term → Term
  /-- Operation number; argument. What an operation computes is not part of the
      language: it is supplied by an `Ops` table (`Reflect.Semantics`). -/
  | prim : Term → Term → Term
  deriving Repr

/-- A program as a data value. Total: there is no term it rejects. -/
def reify : Term → Data
  | .var i => .nat i
  | .app f a => .arr [.nat 0, reify f, reify a]
  | .lam b => .arr [.nat 1, reify b]
  | .lit d => .arr [.nat 2, d]
  | .succ t => .arr [.nat 3, reify t]
  | .cons a b => .arr [.nat 4, reify a, reify b]
  | .dcase s z sc n c => .arr [.nat 5, reify s, reify z, reify sc, reify n, reify c]
  | .prim c x => .arr [.nat 6, reify c, reify x]

/-- Read a program back from its data form. The inverse of `reify`
    (`unreify_reify`). Data that is no program's form is refused. -/
def unreify : Data → Option Term
  | .nat i => some (.var i)
  | .arr [.nat 0, f, a] => do pure (.app (← unreify f) (← unreify a))
  | .arr [.nat 1, b] => do pure (.lam (← unreify b))
  | .arr [.nat 2, d] => some (.lit d)
  | .arr [.nat 3, t] => do pure (.succ (← unreify t))
  | .arr [.nat 4, a, b] => do pure (.cons (← unreify a) (← unreify b))
  | .arr [.nat 5, s, z, sc, n, c] => do
      pure (.dcase (← unreify s) (← unreify z) (← unreify sc) (← unreify n) (← unreify c))
  | .arr [.nat 6, c, x] => do pure (.prim (← unreify c) (← unreify x))
  | _ => none

theorem unreify_reify : ∀ t : Term, unreify (reify t) = some t := by
  intro t
  induction t <;> simp_all [reify, unreify]

end Reflect
