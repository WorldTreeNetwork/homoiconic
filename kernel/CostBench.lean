import Reflect.Arith
import Reflect.RunUntil
import Surface.Read
import Reflect.Interpreter
import Surface.Render
import Wire.Cbor
open Reflect

/-! The worst program found for each operation and each step of the machine's
own that does work on data, run under a budget, timed (`homoiconic-q59.73`).
`lake exe reflectCostBench <case> <size> <budget>` prints one line: the case,
its size, the budget, how the run ended, the wall time, and the wall time per
unit of budget. The size is the depth of doubling, the length of a text, the
bytes of a number or the depth of an environment. Every case but `equal-once`
loops until its budget ends, so the time per unit of budget is the time per
unit of charge. This file only uses what the tree before the change had, so it
measures both. -/

instance : Inhabited Term := ⟨.var 0⟩

def src (s : String) : Term :=
  match Surface.read s.toUTF8 with
  | .ok t => t
  | .error e => panic! e

/-- A number of `k` bytes, every bit set. -/
def bigNat (k : Nat) : Nat := 2 ^ (8 * k) - 1

def textOf (k : Nat) : Data := .text (List.replicate k 'a')

def loopOn (head : String) : String :=
  "def loop x =\n  case " ++ head ++ "\n    0 -> loop x\n    _ -> loop x\n\nloop"

def loopOnArr (head : String) : String :=
  "def loop x =\n  case " ++ head ++ "\n    [] -> loop x\n    _ -> loop x\n\nloop"

def dbl : String :=
  "def dbl x n =\n  case n\n    0 -> x\n    m + 1 -> dbl [x, ...x] m\n\n"

/-- `loop x` reaches a variable `k` places up the environment each time round. -/
def deep (k : Nat) : Term :=
  let body : Term := .app (.lam (.app (.var 1) (.var 1))) (.var k)
  let loop : Term := .app (.lam (.app (.var 0) (.var 0))) (.lam body)
  (List.range k).foldl (fun t _ => .app (.lam t) (.lit (.nat 0))) loop

def caseTerm (name : String) (k : Nat) : Option Term :=
  match name with
  | "loop" => some (.app (src "def loop x = loop x\nloop") (.lit (.nat 0)))
  | "equal-once" => some (.app (src (dbl ++ "fn k -> equal (dbl [0] k) (dbl [0] k)")) (.lit (.nat k)))
  | "equal-doubled" => some (.app (src (dbl ++ loopOn "equal x x" ++ "\n")) (.app (.app (src (dbl ++ "dbl")) (.lit (.arr [.nat 0]))) (.lit (.nat k))))
  | "equal-light" => some (.app (src (loopOn "equal 0 x")) (.app (.app (src (dbl ++ "dbl")) (.lit (.arr [.nat 0]))) (.lit (.nat k))))
  | "equal-text" => some (.app (src (loopOn "equal x x")) (.lit (textOf k)))
  | "equal-big" => some (.app (src (loopOn "equal x x")) (.lit (.nat (bigNat k))))
  | "cons-text" => some (.app (src (loopOnArr "[0, ...x]")) (.lit (textOf k)))
  | "succ-big" => some (.app (src (loopOn "x + 1")) (.lit (.nat (bigNat k))))
  | "case-big" => some (.app (src (loopOn "x")) (.lit (.nat (bigNat k))))
  | "access-deep" => some (deep k)
  | "add-big" => some (.app (src (loopOn "add x x")) (.lit (.nat (bigNat k))))
  | "sub-big" => some (.app (src (loopOn "sub x 1")) (.lit (.nat (bigNat k))))
  | "less-big" => some (.app (src (loopOn "less x x")) (.lit (.nat (bigNat k))))
  | "mul-big" => some (.app (src (loopOn "mul x x")) (.lit (.nat (bigNat k))))
  | "div-big" => some (.app (src (loopOn "div x 3")) (.lit (.nat (bigNat k))))
  | "mod-big" => some (.app (src (loopOn "mod x 3")) (.lit (.nat (bigNat k))))
  | "codes-text" => some (.app (src (loopOnArr "codes x")) (.lit (textOf k)))
  | "text-arr" => some (.app (src (loopOnArr "codes (text x)")) (.lit (.arr (List.replicate k (.nat 97)))))
  | _ => none

def ended : State → String
  | .halted _ => "halted"
  | .running .. => "budget"
  | .fault => "fault"

/-- The steps and the total charge of a run to its end, stopping at `most`
    steps. -/
partial def charged (s : State) (steps total most : Nat) : Nat × Nat × State :=
  match s with
  | .running .. => if steps ≥ most then (steps, total, s) else charged (step s) (steps + 1) (total + stepCost s) most
  | _ => (steps, total, s)

/-- Time one number path on a number of `k` bytes, every bit set
    (`homoiconic-q59.64`): `print` writes it in decimal, `write` makes its byte
    form, `read` reads the byte form back, `source` reads its decimal digits as
    a program. Prints the size of what came out, so nothing is left unrun. -/
def numberPath (kind : String) (k : Nat) : IO Unit := do
  let n := bigNat k
  let bytes := Wire.write (.nat n)
  let digits := (Surface.renderData (.nat n))
  let t0 ← IO.monoNanosNow
  let size ← match kind with
    | "print" => pure (Surface.renderData (.nat (n - 1))).length
    | "write" => pure (Wire.write (.nat (n - 1))).size
    | "read" => pure (match Wire.read bytes with | .ok (.nat v) => Nat.log2 v | _ => 0)
    | "source" => pure (match Surface.read digits.toUTF8 with | .ok (.lit (.nat v)) => Nat.log2 v | _ => 0)
    | _ => pure 0
  let t1 ← IO.monoNanosNow
  IO.println s!"number {kind} bytes={k} out={size} ms={(t1 - t0) / 1000000}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["number", kind, size] => numberPath kind size.toNat!; pure 0
  | ["count", file, levels] =>
    let bytes ← IO.FS.readBinFile file
    match Surface.read bytes with
    | .error e => IO.println s!"{file} {levels} syntax {e}"; pure 0
    | .ok t =>
      let (n, c, e) := charged (load (compile (level levels.toNat! t))) 0 0 200000000
      IO.println s!"{file} levels={levels} steps={n} charge={c} ended={ended e}"
      pure 0
  | [name, size, budget] =>
    match caseTerm name size.toNat!, budget.toNat! with
    | some t, b =>
      let s := load (compile t)
      -- Force the program and its literal before the clock starts.
      if (match s with | .running _ _ _ _ => true | _ => false) then pure () else pure ()
      let t0 ← IO.monoNanosNow
      let e := runPriced b s
      let r := ended e
      let t1 ← IO.monoNanosNow
      let ns := t1 - t0
      IO.println s!"{name} size={size} budget={b} ended={r} ms={ns / 1000000} ns/unit={(ns * 1000 / (max b 1)).toFloat / 1000.0}"
      pure 0
    | none, _ => IO.eprintln s!"no case {name}"; pure 2
  | _ => IO.eprintln "reflectCostBench <case> <size> <budget>"; pure 2
