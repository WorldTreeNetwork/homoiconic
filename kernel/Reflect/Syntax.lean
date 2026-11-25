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
  deriving Repr

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

/-- A program as a data value. Total: there is no term it rejects. What the
    compiler runs is `reifyWalk`, proved equal (`reify_eq_walk`). -/
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
    (`unreify_reify`). Data that is no program's form is refused. What the
    compiler runs is `unreifyWalk`, proved equal (`unreify_eq_walk`). -/
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

/-! ## Walks with a list of work

Data can be nested as deep as a run makes it: a program builds an array a
million arrays deep in a few million steps and a few MiB. A function that
recursed once for each level would fill the native stack of the machine image,
16 MiB, at a few hundred thousand levels (`homoiconic-q59.72`). Each walk here
keeps what is still to do in a list on the heap, calls itself only in tail
position, and is proved equal to the definition the theorems use. `@[csimp]`
makes the compiler run the walk wherever the definition is called. -/

mutual
  /-- Nodes of a data value, each counted once. Only proofs use it: it is the
      measure the walks below terminate by. -/
  def Data.size : Data → Nat
    | .arr xs => Data.sizeList xs + 1
    | _ => 1
  def Data.sizeList : List Data → Nat
    | [] => 0
    | x :: xs => x.size + Data.sizeList xs
end

theorem Data.sizeList_append (xs ys : List Data) :
    Data.sizeList (xs ++ ys) = Data.sizeList xs + Data.sizeList ys := by
  induction xs with
  | nil => simp [Data.sizeList]
  | cons x xs ih => simp [Data.sizeList, ih]; omega

/-- Nodes of a term, each counted once; a literal is one. A measure for proofs. -/
def Term.size : Term → Nat
  | .var _ => 1
  | .lit _ => 1
  | .lam b => b.size + 1
  | .app f a => f.size + a.size + 1
  | .succ t => t.size + 1
  | .cons a b => a.size + b.size + 1
  | .dcase s z sc n c => s.size + z.size + sc.size + n.size + c.size + 1
  | .prim c x => c.size + x.size + 1

/-- What is still to do in `reifyGo`: a term to quote, or a node to build from
    the quoted forms on top of the stack. -/
inductive RAct where
  | term : Term → RAct
  | app | lam | succ | cons | dcase | prim

def RAct.weight : RAct → Nat
  | .term t => 6 * t.size
  | _ => 0

def RAct.weights : List RAct → Nat
  | [] => 0
  | a :: as => a.weight + 1 + RAct.weights as

def reifyGo : List RAct → List Data → Data
  | [], d :: _ => d
  | [], [] => .nat 0
  | .term (.var i) :: as, s => reifyGo as (.nat i :: s)
  | .term (.lit d) :: as, s => reifyGo as (.arr [.nat 2, d] :: s)
  | .term (.app f a) :: as, s => reifyGo (.term f :: .term a :: .app :: as) s
  | .term (.lam b) :: as, s => reifyGo (.term b :: .lam :: as) s
  | .term (.succ t) :: as, s => reifyGo (.term t :: .succ :: as) s
  | .term (.cons a b) :: as, s => reifyGo (.term a :: .term b :: .cons :: as) s
  | .term (.dcase sc z su n c) :: as, s =>
      reifyGo (.term sc :: .term z :: .term su :: .term n :: .term c :: .dcase :: as) s
  | .term (.prim c x) :: as, s => reifyGo (.term c :: .term x :: .prim :: as) s
  | .app :: as, a :: f :: s => reifyGo as (.arr [.nat 0, f, a] :: s)
  | .lam :: as, b :: s => reifyGo as (.arr [.nat 1, b] :: s)
  | .succ :: as, t :: s => reifyGo as (.arr [.nat 3, t] :: s)
  | .cons :: as, b :: a :: s => reifyGo as (.arr [.nat 4, a, b] :: s)
  | .dcase :: as, c :: n :: su :: z :: sc :: s =>
      reifyGo as (.arr [.nat 5, sc, z, su, n, c] :: s)
  | .prim :: as, x :: c :: s => reifyGo as (.arr [.nat 6, c, x] :: s)
  | _ :: as, s => reifyGo as s
termination_by as => RAct.weights as
decreasing_by all_goals simp_wf; all_goals (simp only [RAct.weights, RAct.weight, Term.size]; omega)

theorem reifyGo_term (t : Term) : ∀ as s, reifyGo (.term t :: as) s = reifyGo as (reify t :: s) := by
  induction t with
  | var i => intro as s; rw [reifyGo]; rfl
  | lit d => intro as s; rw [reifyGo]; rfl
  | app f a ihf iha => intro as s; rw [reifyGo, ihf, iha, reifyGo]; rfl
  | lam b ih => intro as s; rw [reifyGo, ih, reifyGo]; rfl
  | succ t ih => intro as s; rw [reifyGo, ih, reifyGo]; rfl
  | cons a b iha ihb => intro as s; rw [reifyGo, iha, ihb, reifyGo]; rfl
  | dcase sc z su n c h1 h2 h3 h4 h5 => intro as s; rw [reifyGo, h1, h2, h3, h4, h5, reifyGo]; rfl
  | prim c x ihc ihx => intro as s; rw [reifyGo, ihc, ihx, reifyGo]; rfl

/-- `reify`, with what is still to quote in a list. -/
def reifyWalk (t : Term) : Data := reifyGo [.term t] []

@[csimp] theorem reify_eq_walk : @reify = @reifyWalk := by
  funext t; simp only [reifyWalk, reifyGo_term]; rw [reifyGo]

/-- What is still to do in `unreifyGo`: data to read as a program, or a node
    to build from the terms on top of the stack. -/
inductive UAct where
  | data : Data → UAct
  | app | lam | succ | cons | dcase | prim

def UAct.weight : UAct → Nat
  | .data d => 4 * d.size
  | _ => 0

def UAct.weights : List UAct → Nat
  | [] => 0
  | a :: as => a.weight + 1 + UAct.weights as

def unreifyGo : List UAct → List Term → Option Term
  | [], t :: _ => some t
  | [], [] => none
  | .data (.nat i) :: as, s => unreifyGo as (.var i :: s)
  | .data (.arr [.nat 0, f, a]) :: as, s => unreifyGo (.data f :: .data a :: .app :: as) s
  | .data (.arr [.nat 1, b]) :: as, s => unreifyGo (.data b :: .lam :: as) s
  | .data (.arr [.nat 2, d]) :: as, s => unreifyGo as (.lit d :: s)
  | .data (.arr [.nat 3, t]) :: as, s => unreifyGo (.data t :: .succ :: as) s
  | .data (.arr [.nat 4, a, b]) :: as, s => unreifyGo (.data a :: .data b :: .cons :: as) s
  | .data (.arr [.nat 5, sc, z, su, n, c]) :: as, s =>
      unreifyGo (.data sc :: .data z :: .data su :: .data n :: .data c :: .dcase :: as) s
  | .data (.arr [.nat 6, c, x]) :: as, s => unreifyGo (.data c :: .data x :: .prim :: as) s
  | .data _ :: _, _ => none
  | .app :: as, a :: f :: s => unreifyGo as (.app f a :: s)
  | .lam :: as, b :: s => unreifyGo as (.lam b :: s)
  | .succ :: as, t :: s => unreifyGo as (.succ t :: s)
  | .cons :: as, b :: a :: s => unreifyGo as (.cons a b :: s)
  | .dcase :: as, c :: n :: su :: z :: sc :: s => unreifyGo as (.dcase sc z su n c :: s)
  | .prim :: as, x :: c :: s => unreifyGo as (.prim c x :: s)
  | _ :: as, s => unreifyGo as s
termination_by as => UAct.weights as
decreasing_by all_goals simp_wf; all_goals (simp only [UAct.weights, UAct.weight, Data.size, Data.sizeList]; omega)

theorem unreifyGo_data (d : Data) : ∀ as s, unreifyGo (.data d :: as) s =
    match unreify d with
    | some t => unreifyGo as (t :: s)
    | none => none := by
  induction d using unreify.induct with
  | case1 i => intro as s; rw [unreifyGo]; rfl
  | case2 f a ihf iha =>
    intro as s; rw [unreifyGo, ihf]; simp only [unreify]
    cases unreify f with
    | none => rfl
    | some tf => simp only [iha]; cases unreify a <;> simp [unreifyGo, bind, Option.bind]
  | case3 b ih => intro as s; rw [unreifyGo, ih]; simp only [unreify]; cases unreify b <;> simp [unreifyGo, bind, Option.bind]
  | case4 d => intro as s; rw [unreifyGo]; rfl
  | case5 t ih => intro as s; rw [unreifyGo, ih]; simp only [unreify]; cases unreify t <;> simp [unreifyGo, bind, Option.bind]
  | case6 a b iha ihb =>
    intro as s; rw [unreifyGo, iha]; simp only [unreify]
    cases unreify a with
    | none => rfl
    | some ta => simp only [ihb]; cases unreify b <;> simp [unreifyGo, bind, Option.bind]
  | case7 sc z su n c h1 h2 h3 h4 h5 =>
    intro as s; rw [unreifyGo, h1]; simp only [unreify]
    cases unreify sc with
    | none => rfl
    | some t1 =>
      simp only [h2]; cases unreify z with
      | none => rfl
      | some t2 =>
        simp only [h3]; cases unreify su with
        | none => rfl
        | some t3 =>
          simp only [h4]; cases unreify n with
          | none => rfl
          | some t4 => simp only [h5]; cases unreify c <;> simp [unreifyGo, bind, Option.bind]
  | case8 c x ihc ihx =>
    intro as s; rw [unreifyGo, ihc]; simp only [unreify]
    cases unreify c with
    | none => rfl
    | some tc => simp only [ihx]; cases unreify x <;> simp [unreifyGo, bind, Option.bind]
  | case9 t n0 n1 n2 n3 n4 n5 n6 n7 =>
    intro as s
    rw [unreify.eq_9 t n0 n1 n2 n3 n4 n5 n6 n7]
    rw [unreifyGo.eq_def]
    split <;> first | rfl | (simp_all; done) | (cases ‹UAct.data t :: as = _ :: _›; simp_all)

/-- `unreify`, with what is still to read in a list. -/
def unreifyWalk (d : Data) : Option Term := unreifyGo [.data d] []

@[csimp] theorem unreify_eq_walk : @unreify = @unreifyWalk := by
  funext d; simp only [unreifyWalk, unreifyGo_data]
  cases unreify d <;> simp [unreifyGo]

/-- A measure for `sameGo`. -/
def pairSizes : List (Data × Data) → Nat
  | [] => 0
  | p :: ps => p.1.size + p.2.size + pairSizes ps

theorem pairSizes_append (ps qs : List (Data × Data)) :
    pairSizes (ps ++ qs) = pairSizes ps + pairSizes qs := by
  induction ps with
  | nil => simp [pairSizes]
  | cons p ps ih => simp [pairSizes, ih]; omega

theorem pairSizes_zip (xs ys : List Data) :
    pairSizes (xs.zip ys) ≤ Data.sizeList xs + Data.sizeList ys := by
  induction xs generalizing ys with
  | nil => simp [pairSizes]
  | cons x xs ih =>
    cases ys with
    | nil => simp [pairSizes]
    | cons y ys => have := ih ys; simp [pairSizes, Data.sizeList]; omega

theorem length_le_sizeList (xs : List Data) : xs.length ≤ Data.sizeList xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have : 1 ≤ x.size := by cases x <;> simp [Data.size]
    simp [Data.sizeList]; omega

/-- Equality of the pairs in `ps`, each pair's sides compared. The items of two
    arrays of one length are paired and wait in the list, so nothing here
    recurses on how deep the data is nested. -/
def sameGo : List (Data × Data) → Bool
  | [] => true
  | (.nat a, .nat b) :: ps => a == b && sameGo ps
  | (.name a, .name b) :: ps => a == b && sameGo ps
  | (.text a, .text b) :: ps => a == b && sameGo ps
  | (.arr xs, .arr ys) :: ps =>
      if xs.length = ys.length then sameGo (xs.zip ys ++ ps) else false
  | _ :: _ => false
termination_by ps => pairSizes ps
decreasing_by
  all_goals simp_wf
  all_goals simp only [pairSizes, pairSizes_append, Data.size]
  all_goals first | omega | (have := pairSizes_zip xs ys; omega)

/-- Whether two data values are equal. The derived `==` of `Data` is opaque to
    proofs and recurses once for each level; this is the equality the
    operation `equal` uses (`Reflect.arith`), proved by `Data.same_iff`. -/
def Data.same (x y : Data) : Bool := sameGo [(x, y)]

theorem zip_all_eq (xs ys : List Data) (h : xs.length = ys.length) :
    (∀ p ∈ xs.zip ys, p.1 = p.2) ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp, List.cons.injEq]
      rw [ih ys h]

theorem sameGo_iff (ps : List (Data × Data)) : sameGo ps = true ↔ ∀ p ∈ ps, p.1 = p.2 := by
  induction ps using sameGo.induct with
  | case1 => simp [sameGo]
  | case2 a b ps ih => simp [sameGo, ih]
  | case3 a b ps ih => simp [sameGo, ih]
  | case4 a b ps ih => simp [sameGo, ih]
  | case5 xs ys ps h ih =>
    rw [sameGo]; simp only [h, ↓reduceIte]; rw [ih]
    simp only [List.mem_append, List.forall_mem_cons]
    constructor
    · intro hp; refine ⟨?_, fun p hp' => hp p (Or.inr hp')⟩
      have := (zip_all_eq xs ys h).1 (fun p hp' => hp p (Or.inl hp')); simp [this]
    · rintro ⟨h1, h2⟩ p (hp | hp)
      · simp at h1; exact (zip_all_eq xs ys h).2 h1 p hp
      · exact h2 p hp
  | case6 xs ys ps h =>
    rw [sameGo]; simp only [h, ↓reduceIte]; simp only [List.forall_mem_cons, Bool.false_eq_true, false_iff]
    rintro ⟨h1, -⟩; simp at h1; exact h (h1 ▸ rfl)
  | case7 p ps n1 n2 n3 n4 =>
    rw [sameGo.eq_def]
    split <;> first | (simp_all; done) | skip
    all_goals
      simp only [Bool.false_eq_true, false_iff]; intro h
      obtain ⟨x, y⟩ := p
      have hp := h _ List.mem_cons_self; simp only at hp; subst hp
      cases x <;> simp_all

theorem Data.same_iff (x y : Data) : Data.same x y = true ↔ x = y := by
  simp [Data.same, sameGo_iff]

/-- `==` on data is `Data.same`. A derived `==` would recurse once for each
    level of nesting and is opaque to proofs. -/
instance : BEq Data := ⟨Data.same⟩

instance : LawfulBEq Data where
  eq_of_beq h := (Data.same_iff _ _).1 h
  rfl := (Data.same_iff _ _).2 rfl

end Reflect
