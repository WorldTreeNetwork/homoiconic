import Reflect.Text

namespace Reflect

/-- First-order data. This is the abstract type; a wire format is elsewhere. -/
inductive Data where
  | nat : Nat → Data
  | arr : List Data → Data
  /-- A channel name. `succ`, `case` and the operation number of `prim` see it
      as its number; nothing in the language makes one. -/
  | name : Nat → Data
  /-- A text: Unicode scalar values in order. `case` and `cons` see it as the
      list of its code points (`Reflect.Text`). -/
  | text : List Char → Data
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

/-- What the compiler runs for `reify`. A `cons` chain is walked by a tail
    call. The definition of `reify` is the recursive one, which the proofs use;
    one call per item overflowed the stack at about 66,000 items. -/
private def reifyFast : Term → Data
  | .var i => .nat i
  | .app f a => .arr [.nat 0, reifyFast f, reifyFast a]
  | .lam b => .arr [.nat 1, reifyFast b]
  | .lit d => .arr [.nat 2, d]
  | .succ t => .arr [.nat 3, reifyFast t]
  | .cons a b => chain [reifyFast a] b
  | .dcase s z sc n c =>
      .arr [.nat 5, reifyFast s, reifyFast z, reifyFast sc, reifyFast n, reifyFast c]
  | .prim c x => .arr [.nat 6, reifyFast c, reifyFast x]
where
  chain (seen : List Data) : Term → Data
    | .cons a b => chain (reifyFast a :: seen) b
    | t => wrap seen (reifyFast t)
  wrap : List Data → Data → Data
    | [], acc => acc
    | h :: hs, acc => wrap hs (.arr [.nat 4, h, acc])

/-- A program as a data value. Total: there is no term it rejects. -/
@[implemented_by reifyFast]
def reify : Term → Data
  | .var i => .nat i
  | .app f a => .arr [.nat 0, reify f, reify a]
  | .lam b => .arr [.nat 1, reify b]
  | .lit d => .arr [.nat 2, d]
  | .succ t => .arr [.nat 3, reify t]
  | .cons a b => .arr [.nat 4, reify a, reify b]
  | .dcase s z sc n c => .arr [.nat 5, reify s, reify z, reify sc, reify n, reify c]
  | .prim c x => .arr [.nat 6, reify c, reify x]

/-- What the compiler runs for `unreify`. A `cons` chain is walked by a tail
    call, matching `reifyFast`. The definition of `unreify` stays the recursive
    one, which the proofs use. -/
private def unreifyFast : Data → Option Term
  | .nat i => some (.var i)
  | .arr [.nat 0, f, a] =>
      match unreifyFast f, unreifyFast a with
      | some f, some a => some (.app f a)
      | _, _ => none
  | .arr [.nat 1, b] => (unreifyFast b).map .lam
  | .arr [.nat 2, d] => some (.lit d)
  | .arr [.nat 3, t] => (unreifyFast t).map .succ
  | .arr [.nat 4, a, b] =>
      match unreifyFast a with
      | some h => chain [h] b
      | none => none
  | .arr [.nat 5, s, z, sc, n, c] =>
      match unreifyFast s, unreifyFast z, unreifyFast sc, unreifyFast n, unreifyFast c with
      | some s, some z, some sc, some n, some c => some (.dcase s z sc n c)
      | _, _, _, _, _ => none
  | .arr [.nat 6, c, x] =>
      match unreifyFast c, unreifyFast x with
      | some c, some x => some (.prim c x)
      | _, _ => none
  | _ => none
where
  chain (seen : List Term) : Data → Option Term
    | .arr [.nat 4, a, b] =>
      match unreifyFast a with
      | some h => chain (h :: seen) b
      | none => none
    | d =>
      match unreifyFast d with
      | some t => some (wrap seen t)
      | none => none
  wrap : List Term → Term → Term
    | [], acc => acc
    | h :: hs, acc => wrap hs (.cons h acc)

/-- Read a program back from its data form. The inverse of `reify`
    (`unreify_reify`). Data that is no program's form is refused. -/
@[implemented_by unreifyFast]
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
