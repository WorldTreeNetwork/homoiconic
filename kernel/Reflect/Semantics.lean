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

/-- A table of operations: operation number and argument to result. Total, so an
    operation has its own answer for an argument it does not expect. Every
    definition and theorem below holds for any table. -/
class Ops where
  op : Nat → Data → Data

variable [Ops]

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
  | succName (h : Direct env t (.value (.data (.name k)))) :
      Direct env (.succ t) (.value (.data (.nat (k + 1))))
  | succText (h : Direct env t (.value (.data (.text cs)))) : Direct env (.succ t) .wrong
  | succClosure (h : Direct env t (.value (.closure b cap))) : Direct env (.succ t) .wrong
  | succError (h : Direct env t e) (he : e.IsError) : Direct env (.succ t) e
  | consArr (ha : Direct env a (.value (.data x)))
      (hb : Direct env b (.value (.data (.arr xs)))) :
      Direct env (.cons a b) (.value (.data (.arr (x :: xs))))
  | consText (ha : Direct env a (.value (.data x)))
      (hb : Direct env b (.value (.data (.text cs)))) :
      Direct env (.cons a b) (.value (.data (.arr (x :: (Text.codes cs).map .nat))))
  | consHeadClosure (ha : Direct env a (.value (.closure c cap))) :
      Direct env (.cons a b) .wrong
  | consHeadError (ha : Direct env a e) (he : e.IsError) : Direct env (.cons a b) e
  | consTailNat (ha : Direct env a (.value (.data x)))
      (hb : Direct env b (.value (.data (.nat k)))) : Direct env (.cons a b) .wrong
  | consTailName (ha : Direct env a (.value (.data x)))
      (hb : Direct env b (.value (.data (.name k)))) : Direct env (.cons a b) .wrong
  | consTailClosure (ha : Direct env a (.value (.data x)))
      (hb : Direct env b (.value (.closure c cap))) : Direct env (.cons a b) .wrong
  | consTailError (ha : Direct env a (.value (.data x)))
      (hb : Direct env b e) (he : e.IsError) : Direct env (.cons a b) e
  | caseZero (hs : Direct env s (.value (.data (.nat 0)))) (h : Direct env z o) :
      Direct env (.dcase s z sc n c) o
  | caseSucc (hs : Direct env s (.value (.data (.nat (k + 1)))))
      (h : Direct (.data (.nat k) :: env) sc o) : Direct env (.dcase s z sc n c) o
  | caseNameZero (hs : Direct env s (.value (.data (.name 0)))) (h : Direct env z o) :
      Direct env (.dcase s z sc n c) o
  | caseNameSucc (hs : Direct env s (.value (.data (.name (k + 1)))))
      (h : Direct (.data (.nat k) :: env) sc o) : Direct env (.dcase s z sc n c) o
  | caseNil (hs : Direct env s (.value (.data (.arr [])))) (h : Direct env n o) :
      Direct env (.dcase s z sc n c) o
  | caseCons (hs : Direct env s (.value (.data (.arr (x :: xs)))))
      (h : Direct (.data (.arr xs) :: .data x :: env) c o) :
      Direct env (.dcase s z sc n c) o
  | caseTextNil (hs : Direct env s (.value (.data (.text [])))) (h : Direct env n o) :
      Direct env (.dcase s z sc n c) o
  | caseTextCons (hs : Direct env s (.value (.data (.text (ch :: r)))))
      (h : Direct (.data (.text r) :: .data (.nat ch.toNat) :: env) c o) :
      Direct env (.dcase s z sc n c) o
  | caseClosure (hs : Direct env s (.value (.closure b cap))) :
      Direct env (.dcase s z sc n c) .wrong
  | caseError (hs : Direct env s e) (he : e.IsError) : Direct env (.dcase s z sc n c) e
  | primCodeError (hc : Direct env c e) (he : e.IsError) : Direct env (.prim c x) e
  | primCodeArr (hc : Direct env c (.value (.data (.arr xs)))) : Direct env (.prim c x) .wrong
  | primCodeText (hc : Direct env c (.value (.data (.text cs)))) : Direct env (.prim c x) .wrong
  | primCodeClosure (hc : Direct env c (.value (.closure b cap))) :
      Direct env (.prim c x) .wrong
  | primArgError (hc : Direct env c (.value (.data (.nat k))))
      (hx : Direct env x e) (he : e.IsError) : Direct env (.prim c x) e
  | primArgClosure (hc : Direct env c (.value (.data (.nat k))))
      (hx : Direct env x (.value (.closure b cap))) : Direct env (.prim c x) .wrong
  | primData (hc : Direct env c (.value (.data (.nat k))))
      (hx : Direct env x (.value (.data d))) :
      Direct env (.prim c x) (.value (.data (Ops.op k d)))
  | primNameArgError (hc : Direct env c (.value (.data (.name k))))
      (hx : Direct env x e) (he : e.IsError) : Direct env (.prim c x) e
  | primNameArgClosure (hc : Direct env c (.value (.data (.name k))))
      (hx : Direct env x (.value (.closure b cap))) : Direct env (.prim c x) .wrong
  | primNameData (hc : Direct env c (.value (.data (.name k))))
      (hx : Direct env x (.value (.data d))) :
      Direct env (.prim c x) (.value (.data (Ops.op k d)))

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
      | some (.value (.data (.name k))) => some (.value (.data (.nat (k + 1))))
      | some (.value (.data (.text _))) => some .wrong
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
          | some (.value (.data (.name _))) => some .wrong
          | some (.value (.data (.text cs))) =>
              some (.value (.data (.arr (x :: (Text.codes cs).map .nat))))
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
      | some (.value (.data (.name 0))) => evalFuel n env z
      | some (.value (.data (.name (k + 1)))) => evalFuel n (.data (.nat k) :: env) sc
      | some (.value (.data (.arr []))) => evalFuel n env ni
      | some (.value (.data (.arr (x :: xs)))) =>
          evalFuel n (.data (.arr xs) :: .data x :: env) c
      | some (.value (.data (.text []))) => evalFuel n env ni
      | some (.value (.data (.text (ch :: r)))) =>
          evalFuel n (.data (.text r) :: .data (.nat ch.toNat) :: env) c
      | some (.value (.closure _ _)) => some .wrong
      | some (.unbound i) => some (.unbound i)
      | some .wrong => some .wrong
  | n + 1, env, .prim c x =>
      match evalFuel n env c with
      | none => none
      | some (.value (.data (.nat k))) =>
          match evalFuel n env x with
          | none => none
          | some (.value (.data d)) => some (.value (.data (Ops.op k d)))
          | some (.value (.closure _ _)) => some .wrong
          | some (.unbound i) => some (.unbound i)
          | some .wrong => some .wrong
      | some (.value (.data (.name k))) =>
          match evalFuel n env x with
          | none => none
          | some (.value (.data d)) => some (.value (.data (Ops.op k d)))
          | some (.value (.closure _ _)) => some .wrong
          | some (.unbound i) => some (.unbound i)
          | some .wrong => some .wrong
      | some (.value (.data (.arr _))) => some .wrong
      | some (.value (.data (.text _))) => some .wrong
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
