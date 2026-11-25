import Wire.Cbor
import Reflect.Machine
import Reflect.Space

/-! What a program and a machine value are as data, so that each has a byte
    form through `Wire.write`.

    A program is its quoted form, `reify`. A function value is the program of
    its body and the values it captured, so code has one form on the wire. -/

namespace Wire
open Reflect

/-- A measure for `codeSameGo`. -/
def codePairs : List (Code × Code) → Nat
  | [] => 0
  | p :: ps => codeSteps p.1 + codeSteps p.2 + codePairs ps

/-- Equality of the pairs of blocks in `ps`. Blocks still to compare wait in
    the list, so nothing here recurses on how deep functions or cases nest. -/
def codeSameGo : List (Code × Code) → Bool
  | [] => true
  | (.done, .done) :: ps => codeSameGo ps
  | (.access i k, .access j k') :: ps => i == j && codeSameGo ((k, k') :: ps)
  | (.closure b k, .closure b' k') :: ps => codeSameGo ((b, b') :: (k, k') :: ps)
  | (.literal d k, .literal d' k') :: ps => Data.same d d' && codeSameGo ((k, k') :: ps)
  | (.checkFun k, .checkFun k') :: ps => codeSameGo ((k, k') :: ps)
  | (.apply k, .apply k') :: ps => codeSameGo ((k, k') :: ps)
  | (.checkData k, .checkData k') :: ps => codeSameGo ((k, k') :: ps)
  | (.succ k, .succ k') :: ps => codeSameGo ((k, k') :: ps)
  | (.cons k, .cons k') :: ps => codeSameGo ((k, k') :: ps)
  | (.dcase z sc n c k, .dcase z' sc' n' c' k') :: ps =>
      codeSameGo ((z, z') :: (sc, sc') :: (n, n') :: (c, c') :: (k, k') :: ps)
  | (.checkNat k, .checkNat k') :: ps => codeSameGo ((k, k') :: ps)
  | (.prim k, .prim k') :: ps => codeSameGo ((k, k') :: ps)
  | _ :: _ => false
termination_by ps => codePairs ps
decreasing_by all_goals simp_wf; all_goals (simp only [codePairs, codeSteps]; omega)

theorem codeSameGo_iff (ps : List (Code × Code)) :
    codeSameGo ps = true ↔ ∀ p ∈ ps, p.1 = p.2 := by
  induction ps using codeSameGo.induct with
  | case1 => simp [codeSameGo]
  | case2 ps ih => rw [codeSameGo, ih]; simp
  | case3 i k j k' ps ih => rw [codeSameGo]; simp only [Bool.and_eq_true, beq_iff_eq, ih]; simp [and_assoc]
  | case4 b k b' k' ps ih => rw [codeSameGo, ih]; simp [and_assoc]
  | case5 d k d' k' ps ih =>
    rw [codeSameGo]; simp only [Bool.and_eq_true, Data.same_iff, ih]; simp [and_assoc]
  | case6 k k' ps ih => rw [codeSameGo, ih]; simp
  | case7 k k' ps ih => rw [codeSameGo, ih]; simp
  | case8 k k' ps ih => rw [codeSameGo, ih]; simp
  | case9 k k' ps ih => rw [codeSameGo, ih]; simp
  | case10 k k' ps ih => rw [codeSameGo, ih]; simp
  | case11 z sc n c k z' sc' n' c' k' ps ih => rw [codeSameGo, ih]; simp [and_assoc]
  | case12 k k' ps ih => rw [codeSameGo, ih]; simp
  | case13 k k' ps ih => rw [codeSameGo, ih]; simp
  | case14 p ps n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 =>
    rw [codeSameGo.eq_14 p ps n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12]
    simp only [Bool.false_eq_true, false_iff]; intro h
    obtain ⟨x, y⟩ := p
    have hp := h _ List.mem_cons_self; simp only at hp; subst hp
    cases x
    · exact n1 rfl
    · exact n2 _ _ _ _ rfl
    · exact n3 _ _ _ _ rfl
    · exact n4 _ _ _ _ rfl
    · exact n5 _ _ rfl
    · exact n6 _ _ rfl
    · exact n7 _ _ rfl
    · exact n8 _ _ rfl
    · exact n9 _ _ rfl
    · exact n10 _ _ _ _ _ _ _ _ _ _ rfl
    · exact n11 _ _ rfl
    · exact n12 _ _ rfl

/-- Whether two blocks of code are equal. -/
def Code.same (a b : Code) : Bool := codeSameGo [(a, b)]

theorem Code.same_iff (a b : Code) : Code.same a b = true ↔ a = b := by
  simp [Code.same, codeSameGo_iff]

/-- The program a block of code was compiled from, when it is exactly the
    compilation of one. `decompile` alone also reads code no compilation
    gives, so the result is compiled again and compared (`Code.same`, which
    decides equality without recursing on how deep the code nests). -/
def blockTerm (c : Code) : Option Term :=
  match decompile c with
  | some t => if Code.same (compile t) c then some t else none
  | none => none

mutual
  /-- A machine value as data: `[0, d]` for data, `[1, body, captured]` for a
      function, where `body` is the quoted program of its code. `none` for a
      function whose code is not the compilation of a program; no compiled
      program makes such a value. -/
  def valueData : MValue → Option Data
    | .data d => some (.arr [.nat 0, d])
    | .closure c env =>
        match blockTerm c, valuesData env with
        | some t, some ds => some (.arr [.nat 1, reify t, .arr ds])
        | _, _ => none
  def valuesData : List MValue → Option (List Data)
    | [] => some []
    | v :: vs =>
        match valueData v, valuesData vs with
        | some d, some ds => some (d :: ds)
        | _, _ => none
end

/-- What is still to do in `valueGo`: a value to give as data, or a function
    to build from its program and the forms of the `n` values it captured, on
    top of the stack. -/
inductive VAct where
  | val : MValue → VAct
  | pack : Nat → Term → VAct

mutual
  /-- Steps `valueGo` takes on a value. A measure for proofs. -/
  def valueSteps : MValue → Nat
    | .data _ => 1
    | .closure _ env => valuesSteps env + 2
  def valuesSteps : List MValue → Nat
    | [] => 0
    | v :: vs => valueSteps v + valuesSteps vs
end

def VAct.steps : VAct → Nat
  | .val v => valueSteps v
  | .pack _ _ => 1

def VAct.total : List VAct → Nat
  | [] => 0
  | a :: as => a.steps + VAct.total as

theorem VAct.total_vals (vs : List MValue) (as : List VAct) :
    VAct.total (vs.map .val ++ as) = valuesSteps vs + VAct.total as := by
  induction vs with
  | nil => simp [valuesSteps]
  | cons v vs ih => simp [VAct.total, VAct.steps, valuesSteps, ih]; omega

def valueGo : List VAct → List Data → Option Data
  | [], d :: _ => some d
  | [], [] => none
  | .val (.data d) :: as, s => valueGo as (.arr [.nat 0, d] :: s)
  | .val (.closure c env) :: as, s =>
      match blockTerm c with
      | some t => valueGo (env.map .val ++ .pack env.length t :: as) s
      | none => none
  | .pack n t :: as, s => valueGo as (.arr [.nat 1, reify t, .arr (s.take n).reverse] :: s.drop n)
termination_by as => VAct.total as
decreasing_by
  all_goals simp_wf
  all_goals simp only [VAct.total, VAct.steps, valueSteps, VAct.total_vals]
  all_goals omega

theorem valuesData_length : ∀ (vs : List MValue) (ds : List Data), valuesData vs = some ds → ds.length = vs.length
  | [], ds, h => by simp [valuesData] at h; subst h; rfl
  | v :: vs, ds, h => by
    simp only [valuesData] at h
    split at h
    · rename_i d ds' hd hds; simp at h; subst h; simp [valuesData_length vs ds' hds]
    · simp at h

mutual
  theorem valueGo_val (v : MValue) (as : List VAct) (s : List Data) :
      valueGo (.val v :: as) s =
        match valueData v with
        | some d => valueGo as (d :: s)
        | none => none := by
    match v with
    | .data d => rw [valueGo]; rfl
    | .closure c env =>
      rw [valueGo]
      simp only [valueData]
      cases hb : blockTerm c with
      | none => simp
      | some t =>
        simp only
        rw [valueGo_vals env]
        cases hv : valuesData env with
        | none => simp
        | some ds =>
          simp only
          rw [valueGo]
          have hl := valuesData_length env ds hv
          rw [← hl, ← List.length_reverse (as := ds), List.take_left, List.drop_left, List.reverse_reverse]
  theorem valueGo_vals (vs : List MValue) (as : List VAct) (s : List Data) :
      valueGo (vs.map .val ++ as) s =
        match valuesData vs with
        | some ds => valueGo as (ds.reverse ++ s)
        | none => none := by
    match vs with
    | [] => simp [valuesData]
    | v :: vs =>
      simp only [List.map_cons, List.cons_append]
      rw [valueGo_val v]
      simp only [valuesData]
      cases hv : valueData v with
      | none => simp
      | some d =>
        simp only
        rw [valueGo_vals vs]
        cases hvs : valuesData vs with
        | none => simp
        | some ds => simp
end

/-- `valueData`, as a walk; the compiler runs it (`valueData_eq_walk`), so a
    chain of functions each capturing the last is written in constant native
    stack (`homoiconic-q59.72`). -/
def valueDataWalk (v : MValue) : Option Data := valueGo [.val v] []

@[csimp] theorem valueData_eq_walk : @valueData = @valueDataWalk := by
  funext v
  simp only [valueDataWalk, valueGo_val]
  cases valueData v <;> simp [valueGo]

mutual
  def dataValue : Data → Option MValue
    | .arr [.nat 0, d] => some (.data d)
    | .arr [.nat 1, body, .arr ds] =>
        match unreify body, dataValues ds with
        | some t, some env => some (.closure (compile t) env)
        | _, _ => none
    | _ => none
  def dataValues : List Data → Option (List MValue)
    | [] => some []
    | d :: ds =>
        match dataValue d, dataValues ds with
        | some v, some vs => some (v :: vs)
        | _, _ => none
end

/-- What is left of `left` after a block of code is counted as its data form
    is built: three hundred for each instruction (the program read back from
    it, the code compiled again to compare, and its quoted form are about that
    many bytes an instruction), and a literal as it is written. `none` when
    it takes more. The code that follows an instruction is a tail call. -/
def codeFits : Code → Nat → Option Nat
  | .done, left => some left
  | .access _ k, left => if 300 ≤ left then codeFits k (left - 300) else none
  | .closure b k, left =>
      if 300 ≤ left then
        match codeFits b (left - 300) with
        | some l => codeFits k l
        | none => none
      else none
  | .literal d k, left =>
      if 300 ≤ left then
        match writesGo (left - 300) [] [d] with
        | some l => codeFits k l
        | none => none
      else none
  | .checkFun k, left => codeFits k left
  | .apply k, left => if 300 ≤ left then codeFits k (left - 300) else none
  | .checkData k, left => codeFits k left
  | .succ k, left => if 300 ≤ left then codeFits k (left - 300) else none
  | .cons k, left => if 300 ≤ left then codeFits k (left - 300) else none
  | .dcase z sc n c k, left =>
      if 300 ≤ left then
        match codeFits z (left - 300) with
        | none => none
        | some l =>
          match codeFits sc l with
          | none => none
          | some l =>
            match codeFits n l with
            | none => none
            | some l =>
              match codeFits c l with
              | none => none
              | some l => codeFits k l
      else none
  | .checkNat k, left => codeFits k left
  | .prim k, left => if 300 ≤ left then codeFits k (left - 300) else none

/-- A measure for `codeFitsGo`. -/
def codesSteps : List Code → Nat
  | [] => 0
  | c :: cs => codeSteps c + codesSteps cs

/-- `codeFits` of each block in the list in turn. Blocks still to count wait
    in the list, so nothing here recurses on how deep functions or cases
    nest. -/
def codeFitsGo : List Code → Nat → Option Nat
  | [], left => some left
  | .done :: ks, left => codeFitsGo ks left
  | .access _ k :: ks, left => if 300 ≤ left then codeFitsGo (k :: ks) (left - 300) else none
  | .closure b k :: ks, left => if 300 ≤ left then codeFitsGo (b :: k :: ks) (left - 300) else none
  | .literal d k :: ks, left =>
      if 300 ≤ left then
        match writesGo (left - 300) [] [d] with
        | some l => codeFitsGo (k :: ks) l
        | none => none
      else none
  | .checkFun k :: ks, left => codeFitsGo (k :: ks) left
  | .apply k :: ks, left => if 300 ≤ left then codeFitsGo (k :: ks) (left - 300) else none
  | .checkData k :: ks, left => codeFitsGo (k :: ks) left
  | .succ k :: ks, left => if 300 ≤ left then codeFitsGo (k :: ks) (left - 300) else none
  | .cons k :: ks, left => if 300 ≤ left then codeFitsGo (k :: ks) (left - 300) else none
  | .dcase z sc n c k :: ks, left =>
      if 300 ≤ left then codeFitsGo (z :: sc :: n :: c :: k :: ks) (left - 300) else none
  | .checkNat k :: ks, left => codeFitsGo (k :: ks) left
  | .prim k :: ks, left => if 300 ≤ left then codeFitsGo (k :: ks) (left - 300) else none
termination_by ks => codesSteps ks
decreasing_by all_goals simp_wf; all_goals (simp only [codesSteps, codeSteps]; omega)

theorem codeFitsGo_cons (c : Code) : ∀ ks left,
    codeFitsGo (c :: ks) left = (codeFits c left).bind (codeFitsGo ks) := by
  induction c with
  | done => intro ks left; rw [codeFitsGo]; rfl
  | access i k ih => intro ks left; rw [codeFitsGo]; simp only [codeFits, ih]; split <;> rfl
  | closure b k ihb ihk =>
    intro ks left; rw [codeFitsGo]; simp only [codeFits]
    split
    · rw [ihb]; cases codeFits b (left - 300) with
      | none => rfl
      | some l => simp [ihk]
    · rfl
  | literal d k ih =>
    intro ks left; rw [codeFitsGo]; simp only [codeFits]
    split
    · cases writesGo (left - 300) [] [d] with
      | none => rfl
      | some l => simp [ih]
    · rfl
  | checkFun k ih => intro ks left; rw [codeFitsGo, ih]; rfl
  | apply k ih => intro ks left; rw [codeFitsGo]; simp only [codeFits, ih]; split <;> rfl
  | checkData k ih => intro ks left; rw [codeFitsGo, ih]; rfl
  | succ k ih => intro ks left; rw [codeFitsGo]; simp only [codeFits, ih]; split <;> rfl
  | cons k ih => intro ks left; rw [codeFitsGo]; simp only [codeFits, ih]; split <;> rfl
  | dcase z sc n c k hz hsc hn hc hk =>
    intro ks left; rw [codeFitsGo]; simp only [codeFits]
    split
    · rw [hz]; cases codeFits z (left - 300) with
      | none => rfl
      | some l =>
        simp only [Option.bind_some]; rw [hsc]; cases codeFits sc l with
        | none => rfl
        | some l =>
          simp only [Option.bind_some]; rw [hn]; cases codeFits n l with
          | none => rfl
          | some l =>
            simp only [Option.bind_some]; rw [hc]; cases codeFits c l with
            | none => rfl
            | some l => simp [hk]
    · rfl
  | checkNat k ih => intro ks left; rw [codeFitsGo, ih]; rfl
  | prim k ih => intro ks left; rw [codeFitsGo]; simp only [codeFits, ih]; split <;> rfl

/-- `codeFits`, as a walk; the compiler runs it (`codeFits_eq_walk`). -/
def codeFitsWalk (c : Code) (left : Nat) : Option Nat := codeFitsGo [c] left

@[csimp] theorem codeFits_eq_walk : @codeFits = @codeFitsWalk := by
  funext c left; simp only [codeFitsWalk, codeFitsGo_cons]
  cases codeFits c left <;> simp [codeFitsGo]

/-- What is left of `left` after the values of `cur` and then of each list of
    `work` are counted as their data forms are written: data as `writesGo`
    counts it, a function its code as `codeFits` counts it and the values it
    captured where they are held, and forty for each value, which is about
    what its data form takes to build beyond what it writes. Captured values
    wait in `work`, so nothing here recurses on how deep functions are
    nested. -/
def valuesFit : (left : Nat) → (work : List (List MValue)) → (cur : List MValue) → Option Nat
  | left, [], [] => some left
  | left, w :: work, [] => valuesFit left work w
  | left, work, .data d :: vs =>
      if _h : 40 ≤ left then
        match writesGo (left - 40) [] [d] with
        | some l => valuesFit (min l (left - 40)) work vs
        | none => none
      else none
  | left, work, .closure c env :: vs =>
      if _h : 40 ≤ left then
        match codeFits c (left - 40) with
        | some l => valuesFit (min l (left - 40)) (vs :: work) env
        | none => none
      else none
termination_by left work => (left, work.length)
decreasing_by
  all_goals simp_wf
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)
  all_goals (apply Prod.Lex.left; omega)

/-- Whether the data form of a machine value can be written in `n` bytes,
    found without building it. `valueData` writes each captured value where it
    is held, so the form of a function can be far larger than what it holds. -/
def fitsValue (v : MValue) (n : Nat) : Bool := (valuesFit n [] [v]).isSome

/-- The byte form of a program: the bytes of its quoted form. -/
def programBytes (t : Term) : ByteArray := write (reify t)

def readProgram (b : ByteArray) : Except String Term := do
  match unreify (← read b) with
  | some t => .ok t
  | none => .error "the value is not a program"

/-- The byte form of a machine value, a waiting program among them. -/
def valueBytes (v : MValue) : Option ByteArray := (valueData v).map write

def readValue (b : ByteArray) : Except String MValue := do
  match dataValue (← read b) with
  | some v => .ok v
  | none => .error "the value is not a machine value"

end Wire
