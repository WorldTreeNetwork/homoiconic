import Reflect.Semantics

namespace Reflect

/-- Code in continuation form: every instruction carries the code that follows
    it. `done` ends a block. A closure body and each case branch is a block. -/
inductive Code where
  | done : Code
  | access : Nat → Code → Code
  | closure : Code → Code → Code
  | literal : Data → Code → Code
  /-- The value on top must be a function, checked before the argument runs. -/
  | checkFun : Code → Code
  | apply : Code → Code
  /-- The value on top must be data, checked before the tail runs. -/
  | checkData : Code → Code
  | succ : Code → Code
  | cons : Code → Code
  | dcase : Code → Code → Code → Code → Code → Code
  /-- The value on top must be a number or a name, checked before the argument runs. -/
  | checkNat : Code → Code
  | prim : Code → Code
  deriving Repr

/-- Postfix flattening: `comp t k` computes `t`, pushes it, and continues as `k`.
    What the compiler runs is `compWalk`, proved equal (`comp_eq_walk`). -/
def comp : Term → Code → Code
  | .var i, k => .access i k
  | .lam b, k => .closure (comp b .done) k
  | .app f a, k => comp f (.checkFun (comp a (.apply k)))
  | .lit d, k => .literal d k
  | .succ t, k => comp t (.succ k)
  | .cons a b, k => comp a (.checkData (comp b (.cons k)))
  | .dcase s z sc n c, k =>
      comp s (.dcase (comp z .done) (comp sc .done) (comp n .done) (comp c .done) k)
  | .prim c x, k => comp c (.checkNat (comp x (.prim k)))

/-- What is still to do in `compGo`. `term t` compiles `t` onto the code on
    top of the stack; `block` pushes an empty block; the rest wrap the code on
    top, or close the blocks on top into one instruction. -/
inductive CAct where
  | term : Term → CAct
  | block | closure | checkFun | apply | checkData | succ | cons | dcase | checkNat | prim

def CAct.weight : CAct → Nat
  | .term t => 10 * t.size
  | _ => 0

def CAct.weights : List CAct → Nat
  | [] => 0
  | a :: as => a.weight + 1 + CAct.weights as

def compGo : List CAct → List Code → Code
  | [], k :: _ => k
  | [], [] => .done
  | .term (.var i) :: as, k :: s => compGo as (.access i k :: s)
  | .term (.lit d) :: as, k :: s => compGo as (.literal d k :: s)
  | .term (.lam b) :: as, s => compGo (.block :: .term b :: .closure :: as) s
  | .term (.app f a) :: as, s => compGo (.apply :: .term a :: .checkFun :: .term f :: as) s
  | .term (.succ t) :: as, s => compGo (.succ :: .term t :: as) s
  | .term (.cons a b) :: as, s => compGo (.cons :: .term b :: .checkData :: .term a :: as) s
  | .term (.dcase sc z su n c) :: as, s =>
      compGo (.block :: .term z :: .block :: .term su :: .block :: .term n :: .block :: .term c ::
        .dcase :: .term sc :: as) s
  | .term (.prim c x) :: as, s => compGo (.prim :: .term x :: .checkNat :: .term c :: as) s
  | .block :: as, s => compGo as (.done :: s)
  | .closure :: as, b :: k :: s => compGo as (.closure b k :: s)
  | .checkFun :: as, k :: s => compGo as (.checkFun k :: s)
  | .apply :: as, k :: s => compGo as (.apply k :: s)
  | .checkData :: as, k :: s => compGo as (.checkData k :: s)
  | .succ :: as, k :: s => compGo as (.succ k :: s)
  | .cons :: as, k :: s => compGo as (.cons k :: s)
  | .dcase :: as, c :: n :: su :: z :: k :: s => compGo as (.dcase z su n c k :: s)
  | .checkNat :: as, k :: s => compGo as (.checkNat k :: s)
  | .prim :: as, k :: s => compGo as (.prim k :: s)
  | _ :: as, s => compGo as s
termination_by as => CAct.weights as
decreasing_by all_goals simp_wf; all_goals (simp only [CAct.weights, CAct.weight, Term.size]; omega)

theorem compGo_term (t : Term) : ∀ as k s, compGo (.term t :: as) (k :: s) = compGo as (comp t k :: s) := by
  induction t with
  | var i => intro as k s; rw [compGo]; rfl
  | lit d => intro as k s; rw [compGo]; rfl
  | lam b ih => intro as k s; rw [compGo, compGo, ih, compGo]; rfl
  | app f a ihf iha => intro as k s; rw [compGo, compGo, iha, compGo, ihf]; rfl
  | succ t ih => intro as k s; rw [compGo, compGo, ih]; rfl
  | cons a b iha ihb => intro as k s; rw [compGo, compGo, ihb, compGo, iha]; rfl
  | dcase sc z su n c h1 h2 h3 h4 h5 =>
    intro as k s
    rw [compGo, compGo, h2, compGo, h3, compGo, h4, compGo, h5, compGo, h1]; rfl
  | prim c x ihc ihx => intro as k s; rw [compGo, compGo, ihx, compGo, ihc]; rfl

/-- `comp`, with what is still to compile in a list: a long list, a deep
    nest of functions or a long chain of calls compiles in constant native
    stack (`homoiconic-q59.72`). -/
def compWalk (t : Term) (k : Code) : Code := compGo [.term t] [k]

@[csimp] theorem comp_eq_walk : @comp = @compWalk := by
  funext t k; simp only [compWalk, compGo_term]; rw [compGo]

def compile (t : Term) : Code := comp t .done

/-- Read code back as a term, with a stack of finished subterms. What the
    compiler runs is `decompWalk`, proved equal (`decomp_eq_walk`). -/
def decomp : Code → List Term → Option Term
  | .done, [t] => some t
  | .done, _ => none
  | .access i k, stk => decomp k (.var i :: stk)
  | .closure b k, stk =>
      match decomp b [] with
      | some t => decomp k (.lam t :: stk)
      | none => none
  | .literal d k, stk => decomp k (.lit d :: stk)
  | .checkFun k, stk => decomp k stk
  | .apply k, a :: f :: stk => decomp k (.app f a :: stk)
  | .apply _, _ => none
  | .checkData k, stk => decomp k stk
  | .succ k, t :: stk => decomp k (.succ t :: stk)
  | .succ _, _ => none
  | .cons k, b :: a :: stk => decomp k (.cons a b :: stk)
  | .cons _, _ => none
  | .dcase z sc n c k, s :: stk =>
      match decomp z [], decomp sc [], decomp n [], decomp c [] with
      | some z', some sc', some n', some c' => decomp k (.dcase s z' sc' n' c' :: stk)
      | _, _, _, _ => none
  | .dcase _ _ _ _ _, [] => none
  | .checkNat k, stk => decomp k stk
  | .prim k, x :: c :: stk => decomp k (.prim c x :: stk)
  | .prim _, _ => none

/-- Steps `decompGo` takes on a block of code. A measure for proofs. -/
def codeSteps : Code → Nat
  | .done => 1
  | .access _ k => codeSteps k + 1
  | .closure b k => codeSteps b + codeSteps k + 2
  | .literal _ k => codeSteps k + 1
  | .checkFun k => codeSteps k + 1
  | .apply k => codeSteps k + 1
  | .checkData k => codeSteps k + 1
  | .succ k => codeSteps k + 1
  | .cons k => codeSteps k + 1
  | .dcase z sc n c k => codeSteps z + codeSteps sc + codeSteps n + codeSteps c + codeSteps k + 5
  | .checkNat k => codeSteps k + 1
  | .prim k => codeSteps k + 1

/-- What is still to do in `decompGo`: a block to read back onto a stack of
    finished subterms, or what to do with a block's term once it is read. -/
inductive DAct where
  | dec : Code → List Term → DAct
  | lam : Code → List Term → DAct
  | dc1 : Code → Code → Code → Code → Term → List Term → DAct
  | dc2 : Code → Code → Code → Term → List Term → DAct
  | dc3 : Code → Code → Term → List Term → DAct
  | dc4 : Code → Term → List Term → DAct

def DAct.steps : DAct → Nat
  | .dec c _ => codeSteps c
  | .lam k _ => codeSteps k + 1
  | .dc1 sc n c k _ _ => codeSteps sc + codeSteps n + codeSteps c + codeSteps k + 4
  | .dc2 n c k _ _ => codeSteps n + codeSteps c + codeSteps k + 3
  | .dc3 c k _ _ => codeSteps c + codeSteps k + 2
  | .dc4 k _ _ => codeSteps k + 1

def DAct.total : List DAct → Nat
  | [] => 0
  | a :: as => a.steps + DAct.total as

def decompGo : List DAct → List Term → Option Term
  | [], t :: _ => some t
  | [], [] => none
  | .dec .done [t] :: as, r => decompGo as (t :: r)
  | .dec .done _ :: _, _ => none
  | .dec (.access i k) stk :: as, r => decompGo (.dec k (.var i :: stk) :: as) r
  | .dec (.closure b k) stk :: as, r => decompGo (.dec b [] :: .lam k stk :: as) r
  | .dec (.literal d k) stk :: as, r => decompGo (.dec k (.lit d :: stk) :: as) r
  | .dec (.checkFun k) stk :: as, r => decompGo (.dec k stk :: as) r
  | .dec (.apply k) (a :: f :: stk) :: as, r => decompGo (.dec k (.app f a :: stk) :: as) r
  | .dec (.apply _) _ :: _, _ => none
  | .dec (.checkData k) stk :: as, r => decompGo (.dec k stk :: as) r
  | .dec (.succ k) (t :: stk) :: as, r => decompGo (.dec k (.succ t :: stk) :: as) r
  | .dec (.succ _) _ :: _, _ => none
  | .dec (.cons k) (b :: a :: stk) :: as, r => decompGo (.dec k (.cons a b :: stk) :: as) r
  | .dec (.cons _) _ :: _, _ => none
  | .dec (.dcase z sc n c k) (s :: stk) :: as, r => decompGo (.dec z [] :: .dc1 sc n c k s stk :: as) r
  | .dec (.dcase _ _ _ _ _) [] :: _, _ => none
  | .dec (.checkNat k) stk :: as, r => decompGo (.dec k stk :: as) r
  | .dec (.prim k) (x :: c :: stk) :: as, r => decompGo (.dec k (.prim c x :: stk) :: as) r
  | .dec (.prim _) _ :: _, _ => none
  | .lam k stk :: as, t :: r => decompGo (.dec k (.lam t :: stk) :: as) r
  | .dc1 sc n c k s stk :: as, r => decompGo (.dec sc [] :: .dc2 n c k s stk :: as) r
  | .dc2 n c k s stk :: as, r => decompGo (.dec n [] :: .dc3 c k s stk :: as) r
  | .dc3 c k s stk :: as, r => decompGo (.dec c [] :: .dc4 k s stk :: as) r
  | .dc4 k s stk :: as, c' :: n' :: sc' :: z' :: r =>
      decompGo (.dec k (.dcase s z' sc' n' c' :: stk) :: as) r
  | _ :: _, _ => none
termination_by as => DAct.total as
decreasing_by all_goals simp_wf; all_goals (simp only [DAct.total, DAct.steps, codeSteps]; omega)

theorem decompGo_dec (c : Code) : ∀ stk as r, decompGo (.dec c stk :: as) r =
    match decomp c stk with
    | some t => decompGo as (t :: r)
    | none => none := by
  induction c with
  | done =>
    intro stk as r
    match stk with
    | [] => rw [decompGo] <;> simp [decomp]
    | [t] => rw [decompGo] <;> simp [decomp]
    | _ :: _ :: _ => rw [decompGo] <;> simp [decomp]
  | access i k ih => intro stk as r; rw [decompGo, ih]; rfl
  | closure b k ihb ihk =>
    intro stk as r; rw [decompGo, ihb]; simp only [decomp]
    cases decomp b [] with
    | none => rfl
    | some tb => simp only; rw [decompGo, ihk]
  | literal d k ih => intro stk as r; rw [decompGo, ih]; rfl
  | checkFun k ih => intro stk as r; rw [decompGo, ih]; rfl
  | apply k ih =>
    intro stk as r
    match stk with
    | [] => rw [decompGo] <;> simp [decomp]
    | [_] => rw [decompGo] <;> simp [decomp]
    | a :: f :: stk => rw [decompGo, ih]; rfl
  | checkData k ih => intro stk as r; rw [decompGo, ih]; rfl
  | succ k ih =>
    intro stk as r
    match stk with
    | [] => rw [decompGo] <;> simp [decomp]
    | t :: stk => rw [decompGo, ih]; rfl
  | cons k ih =>
    intro stk as r
    match stk with
    | [] => rw [decompGo] <;> simp [decomp]
    | [_] => rw [decompGo] <;> simp [decomp]
    | b :: a :: stk => rw [decompGo, ih]; rfl
  | dcase z sc n c k hz hsc hn hc hk =>
    intro stk as r
    match stk with
    | [] => rw [decompGo] <;> simp [decomp]
    | s :: stk =>
      rw [decompGo, hz]; simp only [decomp]
      cases decomp z [] with
      | none => rfl
      | some z' =>
        simp only; rw [decompGo, hsc]
        cases decomp sc [] with
        | none => rfl
        | some sc' =>
          simp only; rw [decompGo, hn]
          cases decomp n [] with
          | none => rfl
          | some n' =>
            simp only; rw [decompGo, hc]
            cases decomp c [] with
            | none => rfl
            | some c' => simp only; rw [decompGo, hk]
  | checkNat k ih => intro stk as r; rw [decompGo, ih]; rfl
  | prim k ih =>
    intro stk as r
    match stk with
    | [] => rw [decompGo] <;> simp [decomp]
    | [_] => rw [decompGo] <;> simp [decomp]
    | x :: c :: stk => rw [decompGo, ih]; rfl

/-- `decomp`, as a walk; the compiler runs it (`decomp_eq_walk`), so code
    nested a million functions deep reads back in constant native stack
    (`homoiconic-q59.72`). -/
def decompWalk (c : Code) (stk : List Term) : Option Term := decompGo [.dec c stk] []

@[csimp] theorem decomp_eq_walk : @decomp = @decompWalk := by
  funext c stk; simp only [decompWalk, decompGo_dec]
  cases decomp c stk <;> simp [decompGo]

def decompile (c : Code) : Option Term := decomp c []

/-- Machine values hold code, not terms. -/
inductive MValue where
  | closure : Code → List MValue → MValue
  | data : Data → MValue
  deriving Repr

abbrev MEnv := List MValue

inductive MOutcome where
  | value : MValue → MOutcome
  | unbound : Nat → MOutcome
  | wrong : MOutcome
  deriving Repr

/-- Where to continue when a block ends. -/
structure Frame where
  code : Code
  env : MEnv
  deriving Repr

inductive State where
  | running : Code → MEnv → List MValue → List Frame → State
  | halted : MOutcome → State
  /-- Not an outcome. A compiled program never reaches it, halting or not
      (`machine_never_faults` in `MachineSafe.lean`). Code that no term
      compiles to can. -/
  | fault : State
  deriving Repr

/-- The frames after entering a block that continues as `k` in `env`. A block
    entered at the end of another (`k` is `done`: a call or a case in tail
    position) pushes no frame. That frame would only end the outer block when
    the inner one ends, and keeping it made a tail loop's frames, and the
    environments they hold, grow with its steps. -/
def push (k : Code) (env : MEnv) (frs : List Frame) : List Frame :=
  match k with
  | .done => frs
  | k => ⟨k, env⟩ :: frs

variable [Ops]

def step : State → State
  | .halted o => .halted o
  | .fault => .fault
  | .running .done _ [v] [] => .halted (.value v)
  | .running .done _ stk (fr :: frs) => .running fr.code fr.env stk frs
  | .running .done _ _ [] => .fault
  | .running (.access i k) env stk frs =>
      match env[i]? with
      | some v => .running k env (v :: stk) frs
      | none => .halted (.unbound i)
  | .running (.closure b k) env stk frs => .running k env (.closure b env :: stk) frs
  | .running (.literal d k) env stk frs => .running k env (.data d :: stk) frs
  | .running (.checkFun k) env (.closure b cap :: stk) frs =>
      .running k env (.closure b cap :: stk) frs
  | .running (.checkFun _) _ (.data _ :: _) _ => .halted .wrong
  | .running (.checkFun _) _ [] _ => .fault
  | .running (.apply k) env (a :: .closure b cap :: stk) frs =>
      .running b (a :: cap) stk (push k env frs)
  | .running (.apply _) _ _ _ => .fault
  | .running (.checkData k) env (.data d :: stk) frs => .running k env (.data d :: stk) frs
  | .running (.checkData _) _ (.closure _ _ :: _) _ => .halted .wrong
  | .running (.checkData _) _ [] _ => .fault
  | .running (.succ k) env (.data (.nat n) :: stk) frs =>
      .running k env (.data (.nat (n + 1)) :: stk) frs
  | .running (.succ k) env (.data (.name n) :: stk) frs =>
      .running k env (.data (.nat (n + 1)) :: stk) frs
  | .running (.succ _) _ (_ :: _) _ => .halted .wrong
  | .running (.succ _) _ [] _ => .fault
  | .running (.cons k) env (.data (.arr xs) :: .data x :: stk) frs =>
      .running k env (.data (.arr (x :: xs)) :: stk) frs
  | .running (.cons k) env (.data (.text cs) :: .data x :: stk) frs =>
      .running k env (.data (.arr (x :: (Text.codes cs).map .nat)) :: stk) frs
  | .running (.cons _) _ (_ :: .data _ :: _) _ => .halted .wrong
  | .running (.cons _) _ _ _ => .fault
  | .running (.dcase z _ _ _ k) env (.data (.nat 0) :: stk) frs =>
      .running z env stk (push k env frs)
  | .running (.dcase _ sc _ _ k) env (.data (.nat (n + 1)) :: stk) frs =>
      .running sc (.data (.nat n) :: env) stk (push k env frs)
  | .running (.dcase z _ _ _ k) env (.data (.name 0) :: stk) frs =>
      .running z env stk (push k env frs)
  | .running (.dcase _ sc _ _ k) env (.data (.name (n + 1)) :: stk) frs =>
      .running sc (.data (.nat n) :: env) stk (push k env frs)
  | .running (.dcase _ _ n _ k) env (.data (.arr []) :: stk) frs =>
      .running n env stk (push k env frs)
  | .running (.dcase _ _ _ c k) env (.data (.arr (x :: xs)) :: stk) frs =>
      .running c (.data (.arr xs) :: .data x :: env) stk (push k env frs)
  | .running (.dcase _ _ n _ k) env (.data (.text []) :: stk) frs =>
      .running n env stk (push k env frs)
  | .running (.dcase _ _ _ c k) env (.data (.text (ch :: r)) :: stk) frs =>
      .running c (.data (.text r) :: .data (.nat ch.toNat) :: env) stk (push k env frs)
  | .running (.dcase _ _ _ _ _) _ (.closure _ _ :: _) _ => .halted .wrong
  | .running (.dcase _ _ _ _ _) _ [] _ => .fault
  | .running (.checkNat k) env (.data (.nat n) :: stk) frs =>
      .running k env (.data (.nat n) :: stk) frs
  | .running (.checkNat k) env (.data (.name n) :: stk) frs =>
      .running k env (.data (.name n) :: stk) frs
  | .running (.checkNat _) _ (_ :: _) _ => .halted .wrong
  | .running (.checkNat _) _ [] _ => .fault
  | .running (.prim k) env (.data d :: .data (.nat n) :: stk) frs =>
      .running k env (.data (Ops.op n d) :: stk) frs
  | .running (.prim _) _ (.closure _ _ :: .data (.nat _) :: _) _ => .halted .wrong
  | .running (.prim k) env (.data d :: .data (.name n) :: stk) frs =>
      .running k env (.data (Ops.op n d) :: stk) frs
  | .running (.prim _) _ (.closure _ _ :: .data (.name _) :: _) _ => .halted .wrong
  | .running (.prim _) _ _ _ => .fault

def run : Nat → State → State
  | 0, s => s
  | n + 1, s => run n (step s)

def load (c : Code) : State := .running c [] [] []

mutual
  /-- A machine value as a source value, by reading its code back. -/
  def readValue : MValue → Option Value
    | .closure c env =>
        match decomp c [], readEnv env with
        | some b, some e => some (.closure b e)
        | _, _ => none
    | .data d => some (.data d)
  def readEnv : List MValue → Option (List Value)
    | [] => some []
    | v :: vs =>
        match readValue v, readEnv vs with
        | some v', some vs' => some (v' :: vs')
        | _, _ => none
end

def readOutcome : MOutcome → Option Outcome
  | .value v => (readValue v).map Outcome.value
  | .unbound i => some (.unbound i)
  | .wrong => some .wrong

/-- Control depth: entries on the value stack plus pending frames. -/
def depth : State → Nat
  | .running _ _ stk frs => stk.length + frs.length
  | _ => 0

end Reflect
