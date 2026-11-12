import Reflect.Arith
import Reflect
open Reflect

/-! Runs the lazy machine on real programs. A program is stopped after some
    steps, its whole state is cut at every value into a store, and the lazy
    machine carries on from the store: with every piece, and with one piece
    withheld and then supplied. Each line that starts with FAIL fails the check. -/

abbrev Cut := StateM (Array (P Nat))

def put (p : P Nat) : Cut (P Nat) := modifyGet fun a => (.ref a.size, a.push p)

/-- Cut at every node: each sub-piece is stored and replaced by its reference. -/
def cutP : P Nat → Cut (P Nat)
  | .nat n => put (.nat n)
  | .nil => put .nil
  | .cons h t => do
      let h' ← cutP h
      let t' ← cutP t
      put (.cons h' t')
  | .closure c e => do
      let e' ← cutP e
      put (.closure c e')
  | .ref r => pure (.ref r)

def cutState : PState Nat → Cut (PState Nat)
  | .running c e stk frs => do
      let e' ← cutP e
      let stk' ← stk.mapM cutP
      let frs' ← frs.mapM fun f => do
        let fe ← cutP f.env
        pure (⟨f.code, fe⟩ : PFrame Nat)
      pure (.running c e' stk' frs')
  | .halted (.value v) => do
      let v' ← cutP v
      pure (.halted (.value v'))
  | s => pure s

def storeOf (a : Array (P Nat)) : Store Nat := fun r => a[r]?
def without (a : Array (P Nat)) (x : Nat) : Store Nat := fun r => if r == x then none else a[r]?

/-- `lstep` until the machine stops, pauses, or the budget ends. -/
def go (σ : Store Nat) : Nat → PState Nat → LRun Nat
  | 0, s => .at s
  | n + 1, s =>
      match s with
      | .halted _ => .at s
      | .fault => .at s
      | _ =>
          match lstep σ s with
          | .next s' => go σ n s'
          | .needs r => .paused r s

partial def resolve (σ : Store Nat) : P Nat → Option (P Nat)
  | .nat n => some (.nat n)
  | .nil => some .nil
  | .cons h t => do
      let h' ← resolve σ h
      let t' ← resolve σ t
      pure (.cons h' t')
  | .closure c e => do
      let e' ← resolve σ e
      pure (.closure c e')
  | .ref r => do
      let p ← σ r
      resolve σ p

def shown (σ : Store Nat) : PState Nat → String
  | .halted (.value v) =>
      match resolve σ v with
      | some p => "value " ++ reprStr p
      | none => "unresolved"
  | .halted (.unbound i) => s!"unbound {i}"
  | .halted .wrong => "wrong"
  | .fault => "fault"
  | _ => "running"

def plain (s : State) : String := shown (fun _ => none) (s.toP : PState Nat)

def budget : Nat := 4000000

/-- Stop `p` after `n` steps, cut everything, and continue lazily. -/
def snapshot (name : String) (p : Term) (n : Nat) : String :=
  let s := run n (load (compile p))
  let want := plain (runUntil budget s)
  let (ps, pieces) := (cutState s.toP).run #[]
  let whole :=
    match go (storeOf pieces) budget ps with
    | .at t => shown (storeOf pieces) t == want
    | .paused _ _ => false
  -- Withhold one piece at a time, for a spread of pieces.
  let stride := pieces.size / 12 + 1
  let picks := (List.range pieces.size).filter (· % stride == 0)
  let results := picks.map fun x =>
    match go (without pieces x) budget ps with
    | .at t => (shown (storeOf pieces) t == want, false)
    | .paused r mid =>
        let again :=
          match go (storeOf pieces) budget mid with
          | .at t => shown (storeOf pieces) t == want
          | .paused _ _ => false
        (r == x && again, true)
  let same := results.all (·.1)
  let paused := (results.filter (·.2)).length
  let ok := whole && same && want != "running"
  s!"{if ok then "ok  " else "FAIL"} {name} after {n} steps: {pieces.size} pieces, whole store {whole}, one piece withheld {picks.length} times (paused {paused}) {same}"

def n (k : Nat) : Term := .lit (.nat k)
def emptyArr : Term := .lit (.arr [])

def programs : List (String × Term) :=
  [ ("identity applied", level 1 (.app identity identity)),
    ("case on array", level 1 (.dcase (.lit (.arr [.nat 4, .nat 5])) (n 0) (n 0) (n 0) (.cons (.var 1) (.var 0)))),
    ("closure over case binder", level 1 (.app (.dcase (n 2) identity (.lam (.var 1)) identity identity) (n 0))),
    ("operation on built operands", level 1 (.prim (n 2) (.cons (.succ (n 5)) (.cons (n 7) emptyArr)))),
    ("function as operand is wrong", level 1 (.prim (n 0) identity)),
    ("unbound variable", level 1 (.app (.var 0) omega)),
    ("builds code and runs it", buildsAndRuns),
    ("interpreter twice", level 2 (.succ (.succ (n 5)))) ]

#eval do
  for (name, p) in programs do
    for k in [0, 7, 40, 300] do
      IO.println (snapshot name p k)

/-- `ask [1] (fn x -> ask [2, x] (fn y -> add x y))` -/
def askTwice : Term :=
  .app (.app askTerm (.lit (.arr [.nat 1])))
    (.lam (.app (.app askTerm (.cons (n 2) (.cons (.var 0) emptyArr)))
      (.lam (.prim (n 0) (.cons (.var 1) (.cons (.var 0) emptyArr))))))

/-- A waiting run is kept in the store and continued from its root. -/
def keptRun : String :=
  match converse 100000 askTwice [.nat 20] with
  | (asked, .waiting k) =>
      let (root, pieces) := (cutP (k.toP : P Nat)).run #[]
      let start : PState Nat := .running (compile (resumeTerm (.nat 22))) (.cons root .nil) [] []
      let got :=
        match go (storeOf pieces) 100000 start with
        | .at t => shown (storeOf pieces) t
        | .paused _ _ => "paused"
      let ok := got == "value " ++ reprStr (P.nat 42 : P Nat) && asked.length == 2
      s!"{if ok then "ok  " else "FAIL"} waiting run kept in {pieces.size} pieces, continued from its root with 22: {got}"
  | _ => "FAIL the program did not wait"

#eval IO.println keptRun
