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

/-- Postfix flattening: `comp t k` computes `t`, pushes it, and continues as `k`. -/
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

def compile (t : Term) : Code := comp t .done

/-- Read code back as a term, with a stack of finished subterms. -/
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
