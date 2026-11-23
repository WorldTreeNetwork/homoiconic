import Reflect.Machine

namespace Reflect

/-- A partial piece of state. One type serves for data, for values and for
    environments: an environment and an array are both `nil` or `cons`. Any
    part may be a reference `ref r` to a piece held in a store. `R` is the kind
    of reference; nothing here says how one is made. -/
inductive P (R : Type) where
  | nat : Nat → P R
  /-- A channel name: a leaf, as a number is. -/
  | name : Nat → P R
  /-- A text: one piece with no parts, so it is never cut. -/
  | text : List Char → P R
  | nil : P R
  | cons : P R → P R → P R
  | closure : Code → P R → P R
  | ref : R → P R
  deriving Repr

/-- A store holds pieces under references and may lack any of them. -/
abbrev Store (R : Type) := R → Option (P R)

/-- `τ` holds every piece `σ` holds. -/
def Store.le {R : Type} (σ τ : Store R) : Prop := ∀ r p, σ r = some p → τ r = some p

/-- Two stores never hold different pieces under one reference. -/
def Store.Compatible {R : Type} (σ τ : Store R) : Prop :=
  ∀ r p q, σ r = some p → τ r = some q → p = q

def Store.union {R : Type} (σ τ : Store R) : Store R := fun r =>
  match σ r with
  | some p => some p
  | none => τ r

variable {R : Type}

mutual
  /-- Data as a piece with no reference in it. -/
  def Data.toP : Data → P R
    | .nat n => .nat n
    | .name n => .name n
    | .text t => .text t
    | .arr xs => Data.listToP xs
  def Data.listToP : List Data → P R
    | [] => .nil
    | x :: xs => .cons x.toP (Data.listToP xs)
end

mutual
  /-- A machine value as a piece with no reference in it. -/
  def MValue.toP : MValue → P R
    | .closure c env => .closure c (envToP env)
    | .data d => d.toP
  def envToP : List MValue → P R
    | [] => .nil
    | v :: vs => .cons v.toP (envToP vs)
end

/-- `Unf σ p q`: following every reference in `p` through `σ` gives `q`, which
    has none. A derivation is finite, so a store with a cycle resolves nothing
    that reaches the cycle. -/
inductive Unf (σ : Store R) : P R → P R → Prop where
  | nat {n} : Unf σ (.nat n) (.nat n)
  | name {n} : Unf σ (.name n) (.name n)
  | text {t} : Unf σ (.text t) (.text t)
  | nil : Unf σ .nil .nil
  | cons {h t h' t'} (hh : Unf σ h h') (ht : Unf σ t t') : Unf σ (.cons h t) (.cons h' t')
  | closure {c e e'} (he : Unf σ e e') : Unf σ (.closure c e) (.closure c e')
  | ref {r p q} (hr : σ r = some p) (hp : Unf σ p q) : Unf σ (.ref r) q

/-- The same, within `n` references deep. -/
inductive UnfD (σ : Store R) : Nat → P R → P R → Prop where
  | nat {d n} : UnfD σ d (.nat n) (.nat n)
  | name {d n} : UnfD σ d (.name n) (.name n)
  | text {d t} : UnfD σ d (.text t) (.text t)
  | nil {d} : UnfD σ d .nil .nil
  | cons {d h t h' t'} (hh : UnfD σ d h h') (ht : UnfD σ d t t') :
      UnfD σ d (.cons h t) (.cons h' t')
  | closure {d c e e'} (he : UnfD σ d e e') : UnfD σ d (.closure c e) (.closure c e')
  | ref {d r p q} (hr : σ r = some p) (hp : UnfD σ d p q) : UnfD σ (d + 1) (.ref r) q

/-- Where to continue when a block ends, with a partial environment. -/
structure PFrame (R : Type) where
  code : Code
  env : P R
  deriving Repr

inductive POutcome (R : Type) where
  | value : P R → POutcome R
  | unbound : Nat → POutcome R
  | wrong : POutcome R
  deriving Repr

/-- A machine state whose environment, stack entries and frame environments
    are partial. `seeking j i cur k env stk frs` is variable lookup under way:
    `access j k` has `i` more entries to pass in `cur`. -/
inductive PState (R : Type) where
  | running : Code → P R → List (P R) → List (PFrame R) → PState R
  | seeking : Nat → Nat → P R → Code → P R → List (P R) → List (PFrame R) → PState R
  | halted : POutcome R → PState R
  | fault : PState R
  deriving Repr

/-- One step of the lazy machine: a next state, or the reference it needs and
    the store lacks. -/
inductive LStep (R : Type) where
  | next : PState R → LStep R
  | needs : R → LStep R

def fetch (σ : Store R) (r : R) (f : P R → PState R) : LStep R :=
  match σ r with
  | some p => .next (f p)
  | none => .needs r

/-- Replace every reference by its piece, one level. -/
def P.hyd (σ : Store R) : P R → Except R (P R)
  | .nat n => .ok (.nat n)
  | .name n => .ok (.name n)
  | .text t => .ok (.text t)
  | .nil => .ok .nil
  | .cons h t =>
      match h.hyd σ, t.hyd σ with
      | .ok h', .ok t' => .ok (.cons h' t')
      | .error r, _ => .error r
      | _, .error r => .error r
  | .closure c e =>
      match e.hyd σ with
      | .ok e' => .ok (.closure c e')
      | .error r => .error r
  | .ref r =>
      match σ r with
      | some p => .ok p
      | none => .error r

/-- A piece that is complete data. -/
def P.toData : P R → Option Data
  | .nat n => some (.nat n)
  | .name n => some (.name n)
  | .text t => some (.text t)
  | .nil => some (.arr [])
  | .cons h t =>
      match h.toData, t.toData with
      | some x, some (.arr xs) => some (.arr (x :: xs))
      | _, _ => none
  | .closure _ _ => none
  | .ref _ => none

def lDone (_env : P R) (stk : List (P R)) (frs : List (PFrame R)) : LStep R :=
  match stk, frs with
  | [v], [] => .next (.halted (.value v))
  | stk, fr :: frs => .next (.running fr.code fr.env stk frs)
  | _, [] => .next .fault

def lSeek (σ : Store R) (j i : Nat) (cur : P R) (k : Code) (env : P R)
    (stk : List (P R)) (frs : List (PFrame R)) : LStep R :=
  match cur, i with
  | .ref r, i => fetch σ r (fun p => .seeking j i p k env stk frs)
  | .nil, _ => .next (.halted (.unbound j))
  | .cons v _, 0 => .next (.running k env (v :: stk) frs)
  | .cons _ t, i + 1 => .next (.seeking j i t k env stk frs)
  | _, _ => .next .fault

def lCheckFun (σ : Store R) (k : Code) (env : P R) (stk : List (P R))
    (frs : List (PFrame R)) : LStep R :=
  match stk with
  | .closure b cap :: stk => .next (.running k env (.closure b cap :: stk) frs)
  | .ref r :: stk => fetch σ r (fun p => .running (.checkFun k) env (p :: stk) frs)
  | _ :: _ => .next (.halted .wrong)
  | [] => .next .fault

def lApply (σ : Store R) (k : Code) (env : P R) (stk : List (P R))
    (frs : List (PFrame R)) : LStep R :=
  match stk with
  | a :: .closure b cap :: stk => .next (.running b (.cons a cap) stk (⟨k, env⟩ :: frs))
  | a :: .ref r :: stk => fetch σ r (fun p => .running (.apply k) env (a :: p :: stk) frs)
  | _ => .next .fault

def lCheckData (σ : Store R) (k : Code) (env : P R) (stk : List (P R))
    (frs : List (PFrame R)) : LStep R :=
  match stk with
  | .closure _ _ :: _ => .next (.halted .wrong)
  | .ref r :: stk => fetch σ r (fun p => .running (.checkData k) env (p :: stk) frs)
  | d :: stk => .next (.running k env (d :: stk) frs)
  | [] => .next .fault

def lSucc (σ : Store R) (k : Code) (env : P R) (stk : List (P R))
    (frs : List (PFrame R)) : LStep R :=
  match stk with
  | .nat n :: stk => .next (.running k env (.nat (n + 1) :: stk) frs)
  | .name n :: stk => .next (.running k env (.nat (n + 1) :: stk) frs)
  | .ref r :: stk => fetch σ r (fun p => .running (.succ k) env (p :: stk) frs)
  | _ :: _ => .next (.halted .wrong)
  | [] => .next .fault

def lCons (σ : Store R) (k : Code) (env : P R) (stk : List (P R))
    (frs : List (PFrame R)) : LStep R :=
  match stk with
  | t :: .ref r :: stk => fetch σ r (fun p => .running (.cons k) env (t :: p :: stk) frs)
  | _ :: .closure _ _ :: _ => .next .fault
  | .ref r :: h :: stk => fetch σ r (fun p => .running (.cons k) env (p :: h :: stk) frs)
  | .nil :: h :: stk => .next (.running k env (.cons h .nil :: stk) frs)
  | .cons a b :: h :: stk => .next (.running k env (.cons h (.cons a b) :: stk) frs)
  | .text t :: h :: stk =>
      .next (.running k env (.cons h (Data.listToP ((Text.codes t).map .nat)) :: stk) frs)
  | _ :: _ :: _ => .next (.halted .wrong)
  | _ => .next .fault

def lCase (σ : Store R) (z sc n c k : Code) (env : P R) (stk : List (P R))
    (frs : List (PFrame R)) : LStep R :=
  match stk with
  | .nat 0 :: stk => .next (.running z env stk (⟨k, env⟩ :: frs))
  | .nat (m + 1) :: stk => .next (.running sc (.cons (.nat m) env) stk (⟨k, env⟩ :: frs))
  | .name 0 :: stk => .next (.running z env stk (⟨k, env⟩ :: frs))
  | .name (m + 1) :: stk => .next (.running sc (.cons (.nat m) env) stk (⟨k, env⟩ :: frs))
  | .nil :: stk => .next (.running n env stk (⟨k, env⟩ :: frs))
  | .cons h t :: stk => .next (.running c (.cons t (.cons h env)) stk (⟨k, env⟩ :: frs))
  | .text [] :: stk => .next (.running n env stk (⟨k, env⟩ :: frs))
  | .text (ch :: r) :: stk =>
      .next (.running c (.cons (.text r) (.cons (.nat ch.toNat) env)) stk (⟨k, env⟩ :: frs))
  | .ref r :: stk => fetch σ r (fun p => .running (.dcase z sc n c k) env (p :: stk) frs)
  | .closure _ _ :: _ => .next (.halted .wrong)
  | [] => .next .fault

def lCheckNat (σ : Store R) (k : Code) (env : P R) (stk : List (P R))
    (frs : List (PFrame R)) : LStep R :=
  match stk with
  | .nat n :: stk => .next (.running k env (.nat n :: stk) frs)
  | .name n :: stk => .next (.running k env (.name n :: stk) frs)
  | .ref r :: stk => fetch σ r (fun p => .running (.checkNat k) env (p :: stk) frs)
  | _ :: _ => .next (.halted .wrong)
  | [] => .next .fault

variable [Ops]

/-- An operation takes complete data, so its argument is hydrated level by
    level until it is. -/
def lPrim (σ : Store R) (k : Code) (env : P R) (stk : List (P R))
    (frs : List (PFrame R)) : LStep R :=
  match stk with
  | x :: .ref r :: stk => fetch σ r (fun p => .running (.prim k) env (x :: p :: stk) frs)
  | .closure _ _ :: .nat _ :: _ => .next (.halted .wrong)
  | x :: .nat n :: stk =>
      match x.toData with
      | some d => .next (.running k env ((Ops.op n d).toP :: stk) frs)
      | none =>
          match x.hyd σ with
          | .ok x' => .next (.running (.prim k) env (x' :: .nat n :: stk) frs)
          | .error r => .needs r
  | .closure _ _ :: .name _ :: _ => .next (.halted .wrong)
  | x :: .name n :: stk =>
      match x.toData with
      | some d => .next (.running k env ((Ops.op n d).toP :: stk) frs)
      | none =>
          match x.hyd σ with
          | .ok x' => .next (.running (.prim k) env (x' :: .name n :: stk) frs)
          | .error r => .needs r
  | _ => .next .fault

/-- The lazy machine. It fetches a piece when a step has to look at one. -/
def lstep (σ : Store R) : PState R → LStep R
  | .halted o => .next (.halted o)
  | .fault => .next .fault
  | .seeking j i cur k env stk frs => lSeek σ j i cur k env stk frs
  | .running .done env stk frs => lDone env stk frs
  | .running (.access i k) env stk frs => .next (.seeking i i env k env stk frs)
  | .running (.closure b k) env stk frs => .next (.running k env (.closure b env :: stk) frs)
  | .running (.literal d k) env stk frs => .next (.running k env (d.toP :: stk) frs)
  | .running (.checkFun k) env stk frs => lCheckFun σ k env stk frs
  | .running (.apply k) env stk frs => lApply σ k env stk frs
  | .running (.checkData k) env stk frs => lCheckData σ k env stk frs
  | .running (.succ k) env stk frs => lSucc σ k env stk frs
  | .running (.cons k) env stk frs => lCons σ k env stk frs
  | .running (.dcase z sc n c k) env stk frs => lCase σ z sc n c k env stk frs
  | .running (.checkNat k) env stk frs => lCheckNat σ k env stk frs
  | .running (.prim k) env stk frs => lPrim σ k env stk frs

/-- The charge for the next lazy step, as `stepCost` charges the plain
    machine. A primitive whose argument is whole data costs what the table
    says. A step that fetches or hydrates its argument, and every other step,
    costs one. -/
def lstepCost : PState R → Nat
  | .running (.prim _) _ (x :: .nat n :: _) _ =>
      match x.toData with
      | some d => Ops.cost n d
      | none => 1
  | .running (.prim _) _ (x :: .name n :: _) _ =>
      match x.toData with
      | some d => Ops.cost n d
      | none => 1
  | _ => 1

/-- Where a lazy run is: at a state, or paused there needing a reference. -/
inductive LRun (R : Type) where
  | at : PState R → LRun R
  | paused : R → PState R → LRun R

def lrun (σ : Store R) : Nat → PState R → LRun R
  | 0, s => .at s
  | n + 1, s =>
      match lstep σ s with
      | .next s' => lrun σ n s'
      | .needs r => .paused r s

/-- A machine state held with no reference in it. -/
def State.toP : State → PState R
  | .running c env stk frs =>
      .running c (envToP env) (stk.map MValue.toP) (frs.map fun f => ⟨f.code, envToP f.env⟩)
  | .halted (.value v) => .halted (.value v.toP)
  | .halted (.unbound i) => .halted (.unbound i)
  | .halted .wrong => .halted .wrong
  | .fault => .fault

/-- Two lists related entry by entry. -/
inductive All2 {α β : Type} (r : α → β → Prop) : List α → List β → Prop where
  | nil : All2 r [] []
  | cons {a b as bs} (h : r a b) (t : All2 r as bs) : All2 r (a :: as) (b :: bs)

def RValue (σ : Store R) (p : P R) (v : MValue) : Prop := Unf σ p v.toP
def REnv (σ : Store R) (p : P R) (env : MEnv) : Prop := Unf σ p (envToP env)

inductive ROutcome (σ : Store R) : POutcome R → MOutcome → Prop where
  | value {p v} (h : RValue σ p v) : ROutcome σ (.value p) (.value v)
  | unbound {i} : ROutcome σ (.unbound i) (.unbound i)
  | wrong : ROutcome σ .wrong .wrong

/-- A partial state resolves to a machine state. A state in the middle of a
    variable lookup resolves to none; lookup finishes within the step. -/
inductive RState (σ : Store R) : PState R → State → Prop where
  | running {c e env stk mstk frs mfrs} (he : REnv σ e env)
      (hs : All2 (RValue σ) stk mstk)
      (hf : All2 (fun (f : PFrame R) (m : Frame) => f.code = m.code ∧ REnv σ f.env m.env)
        frs mfrs) :
      RState σ (.running c e stk frs) (.running c env mstk mfrs)
  | halted {po o} (h : ROutcome σ po o) : RState σ (.halted po) (.halted o)
  | fault : RState σ .fault .fault

end Reflect
