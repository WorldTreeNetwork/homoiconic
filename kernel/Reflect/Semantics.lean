import Reflect.Syntax

namespace Reflect

inductive Value where
  | closure : Term → List Value → Value
  | data : Data → Value
  deriving Repr

abbrev Env := List Value

inductive Outcome where
  | value : Value → Outcome
  | unbound : Nat → Outcome
  | wrong : Outcome
  deriving Repr

/-- The two outcomes that propagate. -/
def Outcome.IsError : Outcome → Prop
  | .value _ => False
  | .unbound _ => True
  | .wrong => True

/-- Function-first call by value. Divergence is the absence of a derivation.
    Each rule has the premises `evalFuel` checks, in the order it checks them. -/
inductive Direct : Env → Term → Outcome → Prop where
  | varBound (h : env[i]? = some v) : Direct env (.var i) (.value v)
  | varUnbound (h : env[i]? = none) : Direct env (.var i) (.unbound i)
  | lam : Direct env (.lam b) (.value (.closure b env))
  | lit : Direct env (.lit d) (.value (.data d))
  | appFunError (hf : Direct env f e) (he : e.IsError) : Direct env (.app f a) e
  | appData (hf : Direct env f (.value (.data d))) : Direct env (.app f a) .wrong
  | appArgError (hf : Direct env f (.value (.closure b cap)))
      (ha : Direct env a e) (he : e.IsError) : Direct env (.app f a) e
  | appValue (hf : Direct env f (.value (.closure b cap)))
      (ha : Direct env a (.value v)) (hb : Direct (v :: cap) b o) :
      Direct env (.app f a) o
  | succNat (h : Direct env t (.value (.data (.nat k)))) :
      Direct env (.succ t) (.value (.data (.nat (k + 1))))
  | succArr (h : Direct env t (.value (.data (.arr xs)))) : Direct env (.succ t) .wrong
  | succClosure (h : Direct env t (.value (.closure b cap))) : Direct env (.succ t) .wrong
  | succError (h : Direct env t e) (he : e.IsError) : Direct env (.succ t) e
  | consArr (ha : Direct env a (.value (.data x)))
      (hb : Direct env b (.value (.data (.arr xs)))) :
      Direct env (.cons a b) (.value (.data (.arr (x :: xs))))
  | consHeadClosure (ha : Direct env a (.value (.closure c cap))) :
      Direct env (.cons a b) .wrong
  | consHeadError (ha : Direct env a e) (he : e.IsError) : Direct env (.cons a b) e
  | consTailNat (ha : Direct env a (.value (.data x)))
      (hb : Direct env b (.value (.data (.nat k)))) : Direct env (.cons a b) .wrong
  | consTailClosure (ha : Direct env a (.value (.data x)))
      (hb : Direct env b (.value (.closure c cap))) : Direct env (.cons a b) .wrong
  | consTailError (ha : Direct env a (.value (.data x)))
      (hb : Direct env b e) (he : e.IsError) : Direct env (.cons a b) e
  | caseZero (hs : Direct env s (.value (.data (.nat 0)))) (h : Direct env z o) :
      Direct env (.dcase s z sc n c) o
  | caseSucc (hs : Direct env s (.value (.data (.nat (k + 1)))))
      (h : Direct (.data (.nat k) :: env) sc o) : Direct env (.dcase s z sc n c) o
  | caseNil (hs : Direct env s (.value (.data (.arr [])))) (h : Direct env n o) :
      Direct env (.dcase s z sc n c) o
  | caseCons (hs : Direct env s (.value (.data (.arr (x :: xs)))))
      (h : Direct (.data (.arr xs) :: .data x :: env) c o) :
      Direct env (.dcase s z sc n c) o
  | caseClosure (hs : Direct env s (.value (.closure b cap))) :
      Direct env (.dcase s z sc n c) .wrong
  | caseError (hs : Direct env s e) (he : e.IsError) : Direct env (.dcase s z sc n c) e

/-- The executable entry. Fuel bounds derivation height. -/
def evalFuel : Nat → Env → Term → Option Outcome
  | 0, _, _ => none
  | _ + 1, env, .var i =>
      match env[i]? with
      | some v => some (.value v)
      | none => some (.unbound i)
  | _ + 1, env, .lam b => some (.value (.closure b env))
  | _ + 1, _, .lit d => some (.value (.data d))
  | n + 1, env, .app f a =>
      match evalFuel n env f with
      | none => none
      | some (.value (.closure b cap)) =>
          match evalFuel n env a with
          | none => none
          | some (.value v) => evalFuel n (v :: cap) b
          | some (.unbound i) => some (.unbound i)
          | some .wrong => some .wrong
      | some (.value (.data _)) => some .wrong
      | some (.unbound i) => some (.unbound i)
      | some .wrong => some .wrong
  | n + 1, env, .succ t =>
      match evalFuel n env t with
      | none => none
      | some (.value (.data (.nat k))) => some (.value (.data (.nat (k + 1))))
      | some (.value (.data (.arr _))) => some .wrong
      | some (.value (.closure _ _)) => some .wrong
      | some (.unbound i) => some (.unbound i)
      | some .wrong => some .wrong
  | n + 1, env, .cons a b =>
      match evalFuel n env a with
      | none => none
      | some (.value (.data x)) =>
          match evalFuel n env b with
          | none => none
          | some (.value (.data (.arr xs))) => some (.value (.data (.arr (x :: xs))))
          | some (.value (.data (.nat _))) => some .wrong
          | some (.value (.closure _ _)) => some .wrong
          | some (.unbound i) => some (.unbound i)
          | some .wrong => some .wrong
      | some (.value (.closure _ _)) => some .wrong
      | some (.unbound i) => some (.unbound i)
      | some .wrong => some .wrong
  | n + 1, env, .dcase s z sc ni c =>
      match evalFuel n env s with
      | none => none
      | some (.value (.data (.nat 0))) => evalFuel n env z
      | some (.value (.data (.nat (k + 1)))) => evalFuel n (.data (.nat k) :: env) sc
      | some (.value (.data (.arr []))) => evalFuel n env ni
      | some (.value (.data (.arr (x :: xs)))) =>
          evalFuel n (.data (.arr xs) :: .data x :: env) c
      | some (.value (.closure _ _)) => some .wrong
      | some (.unbound i) => some (.unbound i)
      | some .wrong => some .wrong

mutual
  /-- A value as data: `[0, body, env]` for a closure, `[1, d]` for data. -/
  def reifyValue : Value → Data
    | .closure b env => .arr [.nat 0, reify b, .arr (reifyEnv env)]
    | .data d => .arr [.nat 1, d]
  def reifyEnv : List Value → List Data
    | [] => []
    | v :: vs => reifyValue v :: reifyEnv vs
end

/-- An outcome as data: `[0, v]`, `[1, i]`, or `[2]`. -/
def reifyOutcome : Outcome → Data
  | .value v => .arr [.nat 0, reifyValue v]
  | .unbound i => .arr [.nat 1, .nat i]
  | .wrong => .arr [.nat 2]

end Reflect
