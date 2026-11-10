namespace Reflect

/-- First-order data. This is the abstract type; a wire format is elsewhere. -/
inductive Data where
  | nat : Nat → Data
  | arr : List Data → Data
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

end Reflect
