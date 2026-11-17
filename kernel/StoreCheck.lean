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
  | .name n => put (.name n)
  | .text t => put (.text t)
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
  | .name n => some (.name n)
  | .text t => some (.text t)
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
def snapshot (name : String) (p : Term) (n : Nat) : String × Nat :=
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
  (s!"{if ok then "ok  " else "FAIL"} {name} after {n} steps: {pieces.size} pieces, whole store {whole}, one piece withheld {picks.length} times (paused {paused}) {same}", paused)

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
  let mut pauses := 0
  for (name, p) in programs do
    for k in [0, 7, 40, 300] do
      let (line, paused) := snapshot name p k
      pauses := pauses + paused
      IO.println line
  -- Without a pause, continuing from a paused state would go untested.
  IO.println s!"{if pauses > 0 then "ok  " else "FAIL"} runs that paused and were continued: {pauses}"

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

/-! Names on the lazy machine. Each of the seven name rules, the program itself
    and the program under `interp`, stopped at four points and cut at every
    value: the lazy machine halts with what the plain machine halts with, with
    the whole store and with a piece withheld. The program itself, cut before
    its first step, also halts with the stated outcome; in the two operations
    with a bad argument that is `unbound` and `wrong`, not `fault`. -/

def nm (k : Nat) : Term := .lit (.name k)

def nameRules : List (String × Term × String) :=
  [ ("name: successor of #3", .succ (nm 3), "value " ++ reprStr (P.nat 4 : P Nat)),
    ("name: cons onto #3", .cons (n 1) (nm 3), "wrong"),
    ("name: case on #0", .dcase (nm 0) (n 7) (n 8) (n 9) (n 9), "value " ++ reprStr (P.nat 7 : P Nat)),
    ("name: case on #3", .dcase (nm 3) (n 7) (.var 0) (n 9) (n 9), "value " ++ reprStr (P.nat 2 : P Nat)),
    ("name: operation #0, unbound argument", .prim (nm 0) (.var 2), "unbound 2"),
    ("name: operation #0 on a function", .prim (nm 0) identity, "wrong"),
    ("name: operation #0 on [2, 3]", .prim (nm 0) (.lit (.arr [.nat 2, .nat 3])),
      "value " ++ reprStr (P.nat 5 : P Nat)),
    ("name: a name is kept as a name", .cons (nm 3) emptyArr,
      "value " ++ reprStr (P.cons (.name 3) .nil : P Nat)) ]

#eval do
  for (name, p, want) in nameRules do
    -- The stated outcome, from a state cut at every value before its first step.
    let s := load (compile p)
    let (ps, pieces) := (cutState s.toP).run #[]
    let got := match go (storeOf pieces) budget ps with
      | .at t => shown (storeOf pieces) t
      | .paused _ _ => "paused"
    IO.println s!"{if got == want && plain (runUntil budget s) == want then "ok  " else "FAIL"} {name} on the lazy machine: {got}"
    for k in [0, 2, 5] do
      IO.println (snapshot name p k).1
    for k in [0, 7, 40, 300] do
      IO.println (snapshot (name ++ ", interpreted") (level 1 p) k).1

/-! Text on the lazy machine. Each of the five text rules, the program itself
    and the program under `interp`, stopped at several points and cut at every
    value, as the name rules are above. A text is a leaf: one piece, taken apart
    by `case` with no fetch beyond the piece itself. -/

def tx (s : String) : Term := .lit (.text s.toList)
def codesP (ks : List Nat) : P Nat := ks.foldr (fun k acc => .cons (.nat k) acc) .nil

def textRules : List (String × Term × String) :=
  [ ("text: successor of \"a\"", .succ (tx "a"), "wrong"),
    ("text: cons 1 onto \"hé\"", .cons (n 1) (tx "hé"), "value " ++ reprStr (codesP [1, 104, 233])),
    ("text: cons 1 onto \"\"", .cons (n 1) (tx ""), "value " ++ reprStr (codesP [1])),
    ("text: case on \"\"", .dcase (tx "") (n 7) (n 8) (n 9) (n 10), "value " ++ reprStr (P.nat 9 : P Nat)),
    ("text: case on \"hé\"",
      .dcase (tx "hé") (n 0) (n 0) (n 0) (.cons (.var 1) (.cons (.var 0) emptyArr)),
      "value " ++ reprStr (P.cons (.nat 104) (.cons (.text "é".toList) .nil) : P Nat)),
    ("text: a text as an operation number", .prim (tx "a") omega, "wrong"),
    ("text: text of [104, 233]", .prim (n 7) (.lit (.arr [.nat 104, .nat 233])),
      "value " ++ reprStr (P.text "hé".toList : P Nat)),
    ("text: codes of \"hé\"", .prim (n 8) (tx "hé"), "value " ++ reprStr (codesP [104, 233])),
    ("text: equal of \"a\" and [97]",
      .prim (n 5) (.cons (tx "a") (.cons (.lit (.arr [.nat 97])) emptyArr)),
      "value " ++ reprStr (P.nat 0 : P Nat)),
    ("text: a text is kept as a text", .cons (tx "a") emptyArr,
      "value " ++ reprStr (P.cons (.text "a".toList) .nil : P Nat)) ]

#eval do
  for (name, p, want) in textRules do
    let s := load (compile p)
    let (ps, pieces) := (cutState s.toP).run #[]
    let got := match go (storeOf pieces) budget ps with
      | .at t => shown (storeOf pieces) t
      | .paused _ _ => "paused"
    IO.println s!"{if got == want && plain (runUntil budget s) == want then "ok  " else "FAIL"} {name} on the lazy machine: {got}"
    for k in [0, 2, 5] do
      IO.println (snapshot name p k).1
    for k in [0, 7, 40, 300] do
      IO.println (snapshot (name ++ ", interpreted") (level 1 p) k).1

-- A stored text is one piece. `case` on a reference to it fetches that piece
-- and no other; with the piece withheld the run pauses needing its reference,
-- and continues once it is there. The same for `cons` onto it.
#eval do
  let pieces : Array (P Nat) := #[.text "hé".toList]
  let onCase : PState Nat :=
    .running (.dcase .done .done .done (.access 1 (.access 0 (.cons .done))) .done) .nil [.ref 0] []
  let onCons : PState Nat := .running (.cons .done) .nil [.ref 0, .nat 1] []
  let paused (s : PState Nat) : Bool := match go (fun _ => none) budget s with
    | .paused r mid => r == 0 && (match go (storeOf pieces) budget mid with
        | .at (.halted (.value _)) => true
        | _ => false)
    | .at _ => false
  let ends (s : PState Nat) (want : P Nat) : Bool := match go (storeOf pieces) budget s with
    | .at t => shown (storeOf pieces) t == "value " ++ reprStr want
    | .paused _ _ => false
  -- `case` binds the head at 1 and the rest at 0; the code conses the head onto the rest.
  let ok := paused onCase && paused onCons && ends onCase (codesP [104, 233]) &&
    ends onCons (codesP [1, 104, 233])
  IO.println s!"{if ok then "ok  " else "FAIL"} a stored text: case and cons fetch its one piece, pause on its reference when it is withheld, and go on when it is supplied"
