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

/-! `Data.toP` and `MValue.toP` recurse once for each level and each item; the
    compiler runs walks over a list of work on the heap, proved equal
    (`homoiconic-q59.78`, as `homoiconic-q59.72` did for the machine). -/



/-- What is still to do in `dataPGo`: data to make a piece of, the items of an
    array to make a list piece of, or a pair to build from the two pieces on
    top of the stack. -/
inductive ToPWork where
  | data : Data → ToPWork
  | list : List Data → ToPWork
  | cons : ToPWork

noncomputable def ToPWork.weight : ToPWork → Nat
  | .data d => 3 * sizeOf d
  | .list xs => 3 * sizeOf xs
  | .cons => 0

noncomputable def ToPWork.weights : List ToPWork → Nat
  | [] => 0
  | a :: as => a.weight + 1 + ToPWork.weights as

def dataPGo : List ToPWork → List (P R) → P R
  | [], p :: _ => p
  | [], [] => .nil
  | .data (.nat n) :: as, s => dataPGo as (.nat n :: s)
  | .data (.name n) :: as, s => dataPGo as (.name n :: s)
  | .data (.text t) :: as, s => dataPGo as (.text t :: s)
  | .data (.arr xs) :: as, s => dataPGo (.list xs :: as) s
  | .list [] :: as, s => dataPGo as (.nil :: s)
  | .list (x :: xs) :: as, s => dataPGo (.data x :: .list xs :: .cons :: as) s
  | .cons :: as, t :: h :: s => dataPGo as (.cons h t :: s)
  | .cons :: as, s => dataPGo as s
termination_by as => ToPWork.weights as
decreasing_by all_goals simp_wf; all_goals (simp [ToPWork.weights, ToPWork.weight] <;> omega)

mutual
  theorem toPGo_data (d : Data) (as : List ToPWork) (s : List (P R)) :
      dataPGo (.data d :: as) s = dataPGo as (d.toP :: s) := by
    match d with
    | .nat n => rw [dataPGo]; rfl
    | .name n => rw [dataPGo]; rfl
    | .text t => rw [dataPGo]; rfl
    | .arr xs => rw [dataPGo, toPGo_list xs]; rfl
  theorem toPGo_list (xs : List Data) (as : List ToPWork) (s : List (P R)) :
      dataPGo (.list xs :: as) s = dataPGo as (Data.listToP xs :: s) := by
    match xs with
    | [] => rw [dataPGo]; rfl
    | x :: xs => rw [dataPGo, toPGo_data x, toPGo_list xs, dataPGo]; rfl
end

def Data.toPWalk (d : Data) : P R := dataPGo [.data d] []

@[csimp] theorem Data.toP_eq_walk : @Data.toP = @Data.toPWalk := by
  funext R d; simp only [Data.toPWalk, toPGo_data]; rw [dataPGo]

def Data.listToPWalk (xs : List Data) : P R := dataPGo [.list xs] []

@[csimp] theorem Data.listToP_eq_walk : @Data.listToP = @Data.listToPWalk := by
  funext R xs; simp only [Data.listToPWalk, toPGo_list]; rw [dataPGo]



mutual
  /-- A machine value as a piece with no reference in it. -/
  def MValue.toP : MValue → P R
    | .closure c env => .closure c (envToP env)
    | .data d => d.toP
  def envToP : List MValue → P R
    | [] => .nil
    | v :: vs => .cons v.toP (envToP vs)
end

/-- What is still to do in `valPGo`. -/
inductive MWork where
  | val : MValue → MWork
  | env : List MValue → MWork
  | cons : MWork
  | close : Code → MWork

noncomputable def MWork.weight : MWork → Nat
  | .val v => 3 * sizeOf v
  | .env vs => 3 * sizeOf vs
  | _ => 0

noncomputable def MWork.weights : List MWork → Nat
  | [] => 0
  | a :: as => a.weight + 1 + MWork.weights as

def valPGo : List MWork → List (P R) → P R
  | [], p :: _ => p
  | [], [] => .nil
  | .val (.data d) :: as, s => valPGo as (d.toP :: s)
  | .val (.closure c env) :: as, s => valPGo (.env env :: .close c :: as) s
  | .env [] :: as, s => valPGo as (.nil :: s)
  | .env (v :: vs) :: as, s => valPGo (.val v :: .env vs :: .cons :: as) s
  | .cons :: as, t :: h :: s => valPGo as (.cons h t :: s)
  | .close c :: as, e :: s => valPGo as (.closure c e :: s)
  | _ :: as, s => valPGo as s
termination_by as => MWork.weights as
decreasing_by all_goals simp_wf; all_goals (simp [MWork.weights, MWork.weight] <;> omega)

mutual
  theorem valPGo_val (v : MValue) (as : List MWork) (s : List (P R)) :
      valPGo (.val v :: as) s = valPGo as (v.toP :: s) := by
    match v with
    | .data d => rw [valPGo]; rfl
    | .closure c env => rw [valPGo, valPGo_env env, valPGo]; rfl
  theorem valPGo_env (vs : List MValue) (as : List MWork) (s : List (P R)) :
      valPGo (.env vs :: as) s = valPGo as (envToP vs :: s) := by
    match vs with
    | [] => rw [valPGo]; rfl
    | v :: vs => rw [valPGo, valPGo_val v, valPGo_env vs, valPGo]; rfl
end

def MValue.toPWalk (v : MValue) : P R := valPGo [.val v] []

@[csimp] theorem MValue.toP_eq_walk : @MValue.toP = @MValue.toPWalk := by
  funext R v; simp only [MValue.toPWalk, valPGo_val]; rw [valPGo]

def envToPWalk (vs : List MValue) : P R := valPGo [.env vs] []

@[csimp] theorem envToP_eq_walk : @envToP = @envToPWalk := by
  funext R vs; simp only [envToPWalk, valPGo_env]; rw [valPGo]


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

/-! `P.hyd` and `P.toData` as walks (`homoiconic-q59.78`). -/

/-- What is still to do in a walk of a piece: a piece to take, or a pair or a
    function to build from what is on top of the stack. -/
inductive PWork (R : Type) where
  | piece : P R → PWork R
  | cons : PWork R
  | close : Code → PWork R

noncomputable def PWork.weight [SizeOf R] : PWork R → Nat
  | .piece p => 3 * sizeOf p
  | _ => 0

noncomputable def PWork.weights [SizeOf R] : List (PWork R) → Nat
  | [] => 0
  | a :: as => a.weight + 1 + PWork.weights as

def pDataGo : List (PWork R) → List Data → Option Data
  | [], d :: _ => some d
  | [], [] => none
  | .piece (.nat n) :: as, s => pDataGo as (.nat n :: s)
  | .piece (.name n) :: as, s => pDataGo as (.name n :: s)
  | .piece (.text t) :: as, s => pDataGo as (.text t :: s)
  | .piece .nil :: as, s => pDataGo as (.arr [] :: s)
  | .piece (.cons h t) :: as, s => pDataGo (.piece h :: .piece t :: .cons :: as) s
  | .piece (.closure _ _) :: _, _ => none
  | .piece (.ref _) :: _, _ => none
  | .cons :: as, .arr xs :: x :: s => pDataGo as (.arr (x :: xs) :: s)
  | .cons :: _, _ => none
  | .close _ :: _, _ => none
termination_by as => PWork.weights (R := R) as
decreasing_by all_goals simp_wf; all_goals (simp [PWork.weights, PWork.weight] <;> omega)

theorem toDataGo_piece (p : P R) : ∀ (as : List (PWork R)) (s : List Data),
    pDataGo (.piece p :: as) s =
      match p.toData with
      | some d => pDataGo as (d :: s)
      | none => none := by
  induction p with
  | nat n => intro as s; rw [pDataGo]; rfl
  | name n => intro as s; rw [pDataGo]; rfl
  | text t => intro as s; rw [pDataGo]; rfl
  | nil => intro as s; rw [pDataGo]; rfl
  | closure c e _ => intro as s; rw [pDataGo]; rfl
  | ref r => intro as s; rw [pDataGo]; rfl
  | cons h t ihh iht =>
    intro as s
    rw [pDataGo, ihh]
    simp only [P.toData]
    cases h.toData with
    | none => rfl
    | some x =>
      simp only
      rw [iht]
      cases ht : t.toData with
      | none => rfl
      | some y =>
        cases y with
        | arr xs => simp only; rw [pDataGo]
        | nat n => simp only; rw [pDataGo]; intros; simp_all
        | name n => simp only; rw [pDataGo]; intros; simp_all
        | text cs => simp only; rw [pDataGo]; intros; simp_all

/-- `P.toData`, as a walk: the compiler runs it (`P.toData_eq_walk`). -/
def P.toDataWalk (p : P R) : Option Data := pDataGo [.piece p] []

@[csimp] theorem P.toData_eq_walk : @P.toData = @P.toDataWalk := by
  funext R p
  simp only [P.toDataWalk, toDataGo_piece]
  cases p.toData <;> simp [pDataGo]

def pHydGo (σ : Store R) : List (PWork R) → List (P R) → Except R (P R)
  | [], p :: _ => .ok p
  | [], [] => .ok .nil
  | .piece (.nat n) :: as, s => pHydGo σ as (.nat n :: s)
  | .piece (.name n) :: as, s => pHydGo σ as (.name n :: s)
  | .piece (.text t) :: as, s => pHydGo σ as (.text t :: s)
  | .piece .nil :: as, s => pHydGo σ as (.nil :: s)
  | .piece (.cons h t) :: as, s => pHydGo σ (.piece h :: .piece t :: .cons :: as) s
  | .piece (.closure c e) :: as, s => pHydGo σ (.piece e :: .close c :: as) s
  | .piece (.ref r) :: as, s =>
      match σ r with
      | some p => pHydGo σ as (p :: s)
      | none => .error r
  | .cons :: as, t :: h :: s => pHydGo σ as (.cons h t :: s)
  | .close c :: as, e :: s => pHydGo σ as (.closure c e :: s)
  | _ :: as, s => pHydGo σ as s
termination_by as => PWork.weights (R := R) as
decreasing_by all_goals simp_wf; all_goals (simp [PWork.weights, PWork.weight] <;> omega)

theorem hydGo_piece (σ : Store R) (p : P R) : ∀ (as : List (PWork R)) (s : List (P R)),
    pHydGo σ (.piece p :: as) s =
      match p.hyd σ with
      | .ok q => pHydGo σ as (q :: s)
      | .error r => .error r := by
  induction p with
  | nat n => intro as s; rw [pHydGo]; rfl
  | name n => intro as s; rw [pHydGo]; rfl
  | text t => intro as s; rw [pHydGo]; rfl
  | nil => intro as s; rw [pHydGo]; rfl
  | ref r => intro as s; rw [pHydGo]; simp only [P.hyd]; cases σ r <;> rfl
  | closure c e ih =>
    intro as s
    rw [pHydGo, ih]
    simp only [P.hyd]
    cases e.hyd σ with
    | error r => rfl
    | ok e' => simp only; rw [pHydGo]
  | cons h t ihh iht =>
    intro as s
    rw [pHydGo, ihh]
    simp only [P.hyd]
    cases h.hyd σ with
    | error r => rfl
    | ok h' =>
      simp only
      rw [iht]
      cases t.hyd σ with
      | error r => rfl
      | ok t' => simp only; rw [pHydGo]

/-- `P.hyd`, as a walk (`P.hyd_eq_walk`). -/
def P.hydWalk (σ : Store R) (p : P R) : Except R (P R) := pHydGo σ [.piece p] []

@[csimp] theorem P.hyd_eq_walk : @P.hyd = @P.hydWalk := by
  funext R σ p
  simp only [P.hydWalk, hydGo_piece]
  cases p.hyd σ <;> simp [pHydGo]

/-- `push` with a partial environment: a block entered in tail position pushes
    no frame. -/
def ppush (k : Code) (env : P R) (frs : List (PFrame R)) : List (PFrame R) :=
  match k with
  | .done => frs
  | k => ⟨k, env⟩ :: frs

@[simp] theorem forall_mem_ppush {k : Code} {env : P R} {frs : List (PFrame R)}
    {q : PFrame R → Prop} :
    (∀ f ∈ ppush k env frs, q f) ↔ (∀ f ∈ frs, q f) ∧ (k ≠ .done → q ⟨k, env⟩) := by
  cases k <;> simp [ppush, and_comm]

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
  | a :: .closure b cap :: stk => .next (.running b (.cons a cap) stk (ppush k env frs))
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
  | .nat 0 :: stk => .next (.running z env stk (ppush k env frs))
  | .nat (m + 1) :: stk => .next (.running sc (.cons (.nat m) env) stk (ppush k env frs))
  | .name 0 :: stk => .next (.running z env stk (ppush k env frs))
  | .name (m + 1) :: stk => .next (.running sc (.cons (.nat m) env) stk (ppush k env frs))
  | .nil :: stk => .next (.running n env stk (ppush k env frs))
  | .cons h t :: stk => .next (.running c (.cons t (.cons h env)) stk (ppush k env frs))
  | .text [] :: stk => .next (.running n env stk (ppush k env frs))
  | .text (ch :: r) :: stk =>
      .next (.running c (.cons (.text r) (.cons (.nat ch.toNat) env)) stk (ppush k env frs))
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

/-- Pieces of a partial value counted as a tree: a pair one and its two parts,
    a function one and its environment, every other piece one. A reference is
    one: it is not followed. -/
def P.nodes : P R → Nat
  | .cons h t => h.nodes + t.nodes + 1
  | .closure _ e => e.nodes + 1
  | _ => 1

def P.nodesList : List (P R) → Nat
  | [] => 0
  | p :: ps => p.nodes + P.nodesList ps

/-- `acc` and the pieces of `work`, or `cap + 1` when that is more: a walk
    that stops once it has counted past `cap`. -/
def nodesGo (cap : Nat) : (work : List (P R)) → (acc : Nat) → Nat
  | [], acc => min acc (cap + 1)
  | p :: ps, acc =>
      if cap < acc then cap + 1
      else match p with
        | .cons h t => nodesGo cap (h :: t :: ps) (acc + 1)
        | .closure _ e => nodesGo cap (e :: ps) (acc + 1)
        | .nat _ => nodesGo cap ps (acc + 1)
        | .name _ => nodesGo cap ps (acc + 1)
        | .text _ => nodesGo cap ps (acc + 1)
        | .nil => nodesGo cap ps (acc + 1)
        | .ref _ => nodesGo cap ps (acc + 1)
termination_by work => P.nodesList work
decreasing_by all_goals simp only [P.nodesList, P.nodes]; omega

theorem nodesGo_eq (cap : Nat) : ∀ (work : List (P R)) (acc : Nat),
    nodesGo cap work acc = min (acc + P.nodesList work) (cap + 1)
  | [], acc => by unfold nodesGo; simp [P.nodesList]
  | p :: ps, acc => by
    unfold nodesGo
    by_cases hc : cap < acc
    · simp only [hc, ite_true]; omega
    · simp only [hc, ite_false]
      cases p with
      | cons h t => simp only []; rw [nodesGo_eq cap (h :: t :: ps)]; simp only [P.nodesList, P.nodes]; omega
      | closure c e => simp only []; rw [nodesGo_eq cap (e :: ps)]; simp only [P.nodesList, P.nodes]; omega
      | nat _ => simp only []; rw [nodesGo_eq cap ps]; simp only [P.nodesList, P.nodes]; omega
      | name _ => simp only []; rw [nodesGo_eq cap ps]; simp only [P.nodesList, P.nodes]; omega
      | text _ => simp only []; rw [nodesGo_eq cap ps]; simp only [P.nodesList, P.nodes]; omega
      | nil => simp only []; rw [nodesGo_eq cap ps]; simp only [P.nodesList, P.nodes]; omega
      | ref _ => simp only []; rw [nodesGo_eq cap ps]; simp only [P.nodesList, P.nodes]; omega
termination_by work => P.nodesList work
decreasing_by all_goals simp only [P.nodesList, P.nodes]; omega

/-- The pieces of `p`, or `cap + 1` when there are more, found by looking at
    no more than `cap + 1` of them. -/
def P.nodesWithin (p : P R) (cap : Nat) : Nat := nodesGo cap [p] 0

theorem P.nodesWithin_eq (p : P R) (cap : Nat) : p.nodesWithin cap = min p.nodes (cap + 1) := by
  simp [P.nodesWithin, nodesGo_eq, P.nodesList]

mutual
  /-- The pieces `d.toP` makes (`Data.nodes_toP`): a number, a name or a text
      one, an array one and, for each item, one and the item. -/
  def Data.nodes : Data → Nat
    | .arr xs => Data.nodesItems xs
    | _ => 1
  def Data.nodesItems : List Data → Nat
    | [] => 1
    | x :: xs => x.nodes + Data.nodesItems xs + 1
end

mutual
  theorem Data.nodes_toP : ∀ d : Data, (d.toP : P R).nodes = d.nodes
    | .nat _ => rfl
    | .name _ => rfl
    | .text _ => rfl
    | .arr xs => by simp only [Data.toP, Data.nodes]; exact Data.nodes_listToP xs
  theorem Data.nodes_listToP : ∀ xs : List Data, (Data.listToP xs : P R).nodes = Data.nodesItems xs
    | [] => rfl
    | x :: xs => by
      simp only [Data.listToP, P.nodes, Data.nodesItems, Data.nodes_toP x, Data.nodes_listToP xs]
end

/-- `Data.nodes`, counted within `cap` by counting the pieces of `d.toP`
    without making them: the lists still to count wait in `work`. -/
def dnodesGo (cap : Nat) : (work : List (List Data)) → (cur : List Data) → (acc : Nat) → Nat
  | [], [], acc => min acc (cap + 1)
  | w :: work, [], acc => dnodesGo cap work w acc
  | work, x :: xs, acc =>
      if cap < acc then cap + 1
      else match x with
        | .arr ys => dnodesGo cap (xs :: work) ys (acc + 2)
        | .nat _ => dnodesGo cap work xs (acc + 2)
        | .name _ => dnodesGo cap work xs (acc + 2)
        | .text _ => dnodesGo cap work xs (acc + 2)
termination_by work cur => sizeOf cur + (work.map sizeOf).sum + work.length
decreasing_by all_goals (simp_wf; (try simp); omega)

def nodesWork : List (List Data) → Nat
  | [] => 0
  | w :: ws => Data.nodesItems w - 1 + nodesWork ws

theorem nodesItems_pos : ∀ xs : List Data, 1 ≤ Data.nodesItems xs
  | [] => by simp [Data.nodesItems]
  | _ :: _ => by simp [Data.nodesItems]

theorem dnodesGo_eq (cap : Nat) : ∀ (work : List (List Data)) (cur : List Data) (acc : Nat),
    dnodesGo cap work cur acc = min (acc + (Data.nodesItems cur - 1) + nodesWork work) (cap + 1)
  | [], [], acc => by unfold dnodesGo; simp [Data.nodesItems, nodesWork]
  | w :: work, [], acc => by
    unfold dnodesGo; rw [dnodesGo_eq cap work w acc]; simp [Data.nodesItems, nodesWork]; omega
  | work, x :: xs, acc => by
    unfold dnodesGo
    have h0 := nodesItems_pos xs
    by_cases hc : cap < acc
    · simp only [hc, ite_true]; omega
    · simp only [hc, ite_false]
      cases x with
      | arr ys =>
        simp only []; rw [dnodesGo_eq cap (xs :: work) ys]
        have := nodesItems_pos ys
        simp only [Data.nodesItems, Data.nodes, nodesWork]; omega
      | nat _ => simp only []; rw [dnodesGo_eq cap work xs]; simp only [Data.nodesItems, Data.nodes]; omega
      | name _ => simp only []; rw [dnodesGo_eq cap work xs]; simp only [Data.nodesItems, Data.nodes]; omega
      | text _ => simp only []; rw [dnodesGo_eq cap work xs]; simp only [Data.nodesItems, Data.nodes]; omega
termination_by work cur => sizeOf cur + (work.map sizeOf).sum + work.length
decreasing_by all_goals (simp_wf; (try simp); omega)

/-- `Data.nodes d`, or `cap + 1` when it is more. -/
def Data.nodesWithin (d : Data) (cap : Nat) : Nat :=
  match d with
  | .arr xs => dnodesGo cap [] xs 1
  | _ => min 1 (cap + 1)

theorem Data.nodesWithin_eq (d : Data) (cap : Nat) : d.nodesWithin cap = min d.nodes (cap + 1) := by
  cases d with
  | arr xs =>
    simp only [Data.nodesWithin, dnodesGo_eq, nodesWork, Data.nodes]
    have := nodesItems_pos xs
    omega
  | _ => rfl

/-- `acc` and the pieces of `work`, with no bound: what the compiler runs
    for `P.nodes` (`P.nodes_eq_walk`). -/
def nodesAll : (work : List (P R)) → (acc : Nat) → Nat
  | [], acc => acc
  | p :: ps, acc =>
      match p with
      | .cons h t => nodesAll (h :: t :: ps) (acc + 1)
      | .closure _ e => nodesAll (e :: ps) (acc + 1)
      | .nat _ => nodesAll ps (acc + 1)
      | .name _ => nodesAll ps (acc + 1)
      | .text _ => nodesAll ps (acc + 1)
      | .nil => nodesAll ps (acc + 1)
      | .ref _ => nodesAll ps (acc + 1)
termination_by work => P.nodesList work
decreasing_by all_goals simp only [P.nodesList, P.nodes]; omega

theorem nodesAll_eq : ∀ (work : List (P R)) (acc : Nat), nodesAll work acc = acc + P.nodesList work
  | [], acc => by unfold nodesAll; simp [P.nodesList]
  | p :: ps, acc => by
      unfold nodesAll
      cases p with
      | cons h t => simp only []; rw [nodesAll_eq (h :: t :: ps)]; simp only [P.nodesList, P.nodes]; omega
      | closure c e => simp only []; rw [nodesAll_eq (e :: ps)]; simp only [P.nodesList, P.nodes]; omega
      | nat _ => simp only []; rw [nodesAll_eq ps]; simp only [P.nodesList, P.nodes]; omega
      | name _ => simp only []; rw [nodesAll_eq ps]; simp only [P.nodesList, P.nodes]; omega
      | text _ => simp only []; rw [nodesAll_eq ps]; simp only [P.nodesList, P.nodes]; omega
      | nil => simp only []; rw [nodesAll_eq ps]; simp only [P.nodesList, P.nodes]; omega
      | ref _ => simp only []; rw [nodesAll_eq ps]; simp only [P.nodesList, P.nodes]; omega
termination_by work => P.nodesList work
decreasing_by all_goals simp only [P.nodesList, P.nodes]; omega

def P.nodesWalk (p : P R) : Nat := nodesAll [p] 0

@[csimp] theorem P.nodes_eq_walk : @P.nodes = @P.nodesWalk := by
  funext R p; simp [P.nodesWalk, nodesAll_eq, P.nodesList]

/-- `dnodesGo` with no bound: what the compiler runs for `Data.nodes`. -/
def dnodesAll : (work : List (List Data)) → (cur : List Data) → (acc : Nat) → Nat
  | [], [], acc => acc
  | w :: work, [], acc => dnodesAll work w acc
  | work, x :: xs, acc =>
      match x with
      | .arr ys => dnodesAll (xs :: work) ys (acc + 2)
      | .nat _ => dnodesAll work xs (acc + 2)
      | .name _ => dnodesAll work xs (acc + 2)
      | .text _ => dnodesAll work xs (acc + 2)
termination_by work cur => sizeOf cur + (work.map sizeOf).sum + work.length
decreasing_by all_goals (simp_wf; (try simp); omega)

theorem dnodesAll_eq : ∀ (work : List (List Data)) (cur : List Data) (acc : Nat),
    dnodesAll work cur acc = acc + (Data.nodesItems cur - 1) + nodesWork work
  | [], [], acc => by unfold dnodesAll; simp [Data.nodesItems, nodesWork]
  | w :: work, [], acc => by
    unfold dnodesAll; rw [dnodesAll_eq work w acc]; simp [Data.nodesItems, nodesWork]; omega
  | work, x :: xs, acc => by
    unfold dnodesAll
    have h0 := nodesItems_pos xs
    cases x with
    | arr ys =>
      simp only []; rw [dnodesAll_eq (xs :: work) ys]
      have := nodesItems_pos ys
      simp only [Data.nodesItems, Data.nodes, nodesWork]; omega
      | nat _ => simp only []; rw [dnodesAll_eq work xs]; simp only [Data.nodesItems, Data.nodes]; omega
      | name _ => simp only []; rw [dnodesAll_eq work xs]; simp only [Data.nodesItems, Data.nodes]; omega
      | text _ => simp only []; rw [dnodesAll_eq work xs]; simp only [Data.nodesItems, Data.nodes]; omega
termination_by work cur => sizeOf cur + (work.map sizeOf).sum + work.length
decreasing_by all_goals (simp_wf; (try simp); omega)

def Data.nodesWalk (d : Data) : Nat :=
  match d with
  | .arr xs => dnodesAll [] xs 1
  | _ => 1

@[csimp] theorem Data.nodes_eq_walk : @Data.nodes = @Data.nodesWalk := by
  funext d
  cases d with
  | arr xs =>
    simp only [Data.nodesWalk, dnodesAll_eq, nodesWork, Data.nodes]
    have := nodesItems_pos xs
    omega
  | _ => rfl

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

/-- Pieces of a literal a unit of budget pays for making (`d.toP`)
    (`bound-kept-sessions`, `homoiconic-q59.80`). Chosen by measurement
    (`kernel/CostBench.lean`, `lazy` cases). -/
def convUnit : Nat := 8

/-- Pieces of an operation's argument converted with no charge: an array of
    three numbers is seven, a pair five. Each piece past these is charged one:
    converting a piece to data, twice, and counting it, takes about ten times
    what a literal's piece takes (`kernel/CostBench.lean`, `add-doubled`). -/
def convFree : Nat := 7

/-- The charge for an operation on the argument `x`: what the table says when
    `x` is whole data, one when it is not and the step hydrates it, and in
    both cases one for each piece of `x` past `convFree`, which the step walks
    (`P.toData`, `P.hyd`). -/
def primCost (n : Nat) (x : P R) : Nat :=
  (match x.toData with
   | some d => Ops.cost n d
   | none => 1) + (x.nodes - convFree)

/-- An operation's charge on the argument `x` as `lPrim` takes it: a
    function halts `wrong` and walks nothing, so it is charged one. -/
def primCharge (n : Nat) (x : P R) : Nat :=
  match x with
  | .closure _ _ => 1
  | x => primCost n x

/-- The conversion's part of `primCharge`, which a count of pieces gives. -/
def primFloor (x : P R) : Nat :=
  match x with
  | .closure _ _ => 0
  | x => x.nodes - convFree

theorem primFloor_le (n : Nat) (x : P R) : primFloor x ≤ primCharge n x := by
  cases x <;> simp only [primFloor, primCharge, primCost] <;> omega

/-- The charge for the next lazy step, as `stepCost` charges the plain
    machine, and the conversions the lazy machine makes on top. An operation
    is charged `primCost`: the table's cost and its argument's pieces past
    `convFree`. A literal is one and one for every `convUnit` of its pieces
    (`Data.nodes`), which `d.toP` makes. `succ`
    or `case` of a number and `cons` onto a text cost what the table says for
    that data (`Ops.work`); reaching a variable is a step for each place
    passed, so it costs one a step. A fetch, and every other step, costs one.
    A function as an operation's argument halts `wrong` and walks nothing:
    one. So it agrees with `stepCost` on an operation whose argument has at
    most `convFree` pieces and on a literal of fewer than `convUnit`, and is
    never less. -/
def lstepCost : PState R → Nat
  | .running (.prim _) _ (x :: .nat n :: _) _ => primCharge n x
  | .running (.prim _) _ (x :: .name n :: _) _ => primCharge n x
  | .running (.literal d _) _ _ _ => 1 + d.nodes / convUnit
  | .running (.succ _) _ (.nat n :: _) _ => Ops.work (.nat n)
  | .running (.succ _) _ (.name n :: _) _ => Ops.work (.name n)
  | .running (.dcase _ _ _ _ _) _ (.nat n :: _) _ => Ops.work (.nat n)
  | .running (.dcase _ _ _ _ _) _ (.name n :: _) _ => Ops.work (.name n)
  | .running (.cons _) _ (.text t :: _) _ => Ops.work (.text t)
  | _ => 1

/-- `primCost n x`, or `cap + 1` when it is more, found by counting `x`'s
    pieces within what `cap` pays for and converting `x` only when they are
    within it (`primCostWithin_eq`). -/
def primCostWithin (n : Nat) (x : P R) (cap : Nat) : Nat :=
  let w := x.nodesWithin (cap + convFree)
  if cap + convFree + 1 ≤ w then cap + 1
  else
    match x.toData with
    | some d => (w - convFree) + Ops.costWithin n d (cap - (w - convFree))
    | none => min (1 + (w - convFree)) (cap + 1)

theorem primCostWithin_eq (n : Nat) (x : P R) (cap : Nat) :
    primCostWithin n x cap = min (primCost n x) (cap + 1) := by
  unfold primCostWithin primCost
  simp only [P.nodesWithin_eq, convFree]
  by_cases h : cap + 7 + 1 ≤ min x.nodes (cap + 7 + 1)
  · simp only [h, ite_true]
    omega
  · simp only [h, ite_false]
    have hw : min x.nodes (cap + 7 + 1) = x.nodes := by omega
    rw [hw]
    have : x.nodes - 7 ≤ cap := by omega
    cases x.toData with
    | some d => simp only; rw [Ops.costWithin_eq]; omega
    | none => simp only

/-- A literal's charge, or `cap + 1` when it is more. -/
def literalCostWithin (d : Data) (cap : Nat) : Nat :=
  let w := d.nodesWithin (convUnit * (cap + 1))
  if convUnit * (cap + 1) ≤ w then cap + 1 else min (1 + w / convUnit) (cap + 1)

omit [Ops] in
theorem literalCostWithin_eq (d : Data) (cap : Nat) :
    literalCostWithin d cap = min (1 + d.nodes / convUnit) (cap + 1) := by
  unfold literalCostWithin
  simp only [Data.nodesWithin_eq, convUnit]
  split <;> omega

def primChargeWithin (n : Nat) (x : P R) (cap : Nat) : Nat :=
  match x with
  | .closure _ _ => min 1 (cap + 1)
  | x => primCostWithin n x cap

theorem primChargeWithin_eq (n : Nat) (x : P R) (cap : Nat) :
    primChargeWithin n x cap = min (primCharge n x) (cap + 1) := by
  cases x <;> simp only [primChargeWithin, primCharge, primCostWithin_eq]

def primFloorWithin (x : P R) (cap : Nat) : Nat :=
  match x with
  | .closure _ _ => 0
  | x => x.nodesWithin (cap + convFree) - convFree

omit [Ops] in
theorem primFloorWithin_eq (x : P R) (cap : Nat) :
    primFloorWithin x cap = min (primFloor x) (cap + 1) := by
  cases x <;> simp only [primFloorWithin, primFloor, P.nodesWithin_eq, convFree] <;> omega

/-- `lstepCost s`, or `cap + 1` when it is more, found in time that `cap`
    bounds: an argument or a literal is counted within what `cap` pays for
    before it is converted (`lstepCostWithin_eq`). -/
def lstepCostWithin (s : PState R) (cap : Nat) : Nat :=
  match s with
  | .running (.prim _) _ (x :: .nat n :: _) _ => primChargeWithin n x cap
  | .running (.prim _) _ (x :: .name n :: _) _ => primChargeWithin n x cap
  | .running (.literal d _) _ _ _ => literalCostWithin d cap
  | s => min (lstepCost s) (cap + 1)

theorem lstepCostWithin_eq (s : PState R) (cap : Nat) :
    lstepCostWithin s cap = min (lstepCost s) (cap + 1) := by
  unfold lstepCostWithin
  split
  · rw [primChargeWithin_eq]; rfl
  · rw [primChargeWithin_eq]; rfl
  · rw [literalCostWithin_eq]; rfl
  · rfl

/-- A floor of the charge that converts nothing: the conversion's part of an
    operation's or a literal's charge, from a count of pieces. A run asks it
    before it affords the step's cells, and the charge only after, so no
    conversion is made before the run could refuse it for space. -/
def lfloor : PState R → Nat
  | .running (.prim _) _ (x :: .nat _ :: _) _ => primFloor x
  | .running (.prim _) _ (x :: .name _ :: _) _ => primFloor x
  | .running (.literal d _) _ _ _ => 1 + d.nodes / convUnit
  | _ => 0

theorem lfloor_le (s : PState R) : lfloor s ≤ lstepCost s := by
  unfold lfloor lstepCost
  split
  · exact primFloor_le _ _
  · exact primFloor_le _ _
  · exact Nat.le_refl _
  · exact Nat.zero_le _

/-- `lfloor s`, or `cap + 1` when it is more, looking at no more pieces than
    `cap` pays for. -/
def lfloorWithin (s : PState R) (cap : Nat) : Nat :=
  match s with
  | .running (.prim _) _ (x :: .nat _ :: _) _ => primFloorWithin x cap
  | .running (.prim _) _ (x :: .name _ :: _) _ => primFloorWithin x cap
  | .running (.literal d _) _ _ _ => literalCostWithin d cap
  | _ => 0

theorem lfloorWithin_eq (s : PState R) (cap : Nat) : lfloorWithin s cap = min (lfloor s) (cap + 1) := by
  unfold lfloorWithin lfloor
  split
  · exact primFloorWithin_eq _ _
  · exact primFloorWithin_eq _ _
  · rw [literalCostWithin_eq]
  · simp

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
