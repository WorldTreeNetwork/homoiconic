import Reflect.Arith
import Reflect.Interpreter
import Reflect.Machine
open Reflect

/-- Step until the machine stops; return the number of steps and the final state. -/
partial def runCount (s : State) (n : Nat := 0) : Nat × State :=
  match s with
  | .running .. => runCount (step s) (n + 1)
  | _ => (n, s)

/-- Count down from a literal by recursion through the fixed point. -/
def countdown (k : Nat) : Term :=
  .app (B.compile [] (.app B.fix (B.lams ["go", "n"]
    (.dcase (B.v "n") (B.num 0) "m" (.app (B.v "go") (B.v "m")) B.W "_" "_" B.W))))
    (.lit (.nat k))

/-- Count the items of a list by `case`: `go xs acc`. On a text each step of
    `case` hands over the first code point and the rest, a text. -/
def walk : Term :=
  .app (B.compile [] B.fix) (.lam (.lam (.lam
    (.dcase (.var 1) (.app (.lit (.nat 0)) (.lit (.nat 0))) (.app (.lit (.nat 0)) (.lit (.nat 0)))
      (.var 0) (.app (.app (.var 4) (.var 0)) (.succ (.var 2)))))))

/-- A text of `k` characters. -/
def sample (k : Nat) : Data := .text ((List.range k).map fun i => Char.ofNat (97 + i % 26))

/-- The walk over the text itself. -/
def caseWalk (k : Nat) : Term := .app (.app walk (.lit (sample k))) (.lit (.nat 0))

/-- The walk over the array `codes` (operation 8) makes of the text. -/
def codesWalk (k : Nat) : Term :=
  .app (.app walk (.prim (.lit (.nat 8)) (.lit (sample k)))) (.lit (.nat 0))

/-- `codes` alone: one step of the machine, linear in the text. -/
def codesOnly (k : Nat) : Term :=
  .dcase (.prim (.lit (.nat 8)) (.lit (sample k))) (.lit (.nat 0)) (.lit (.nat 0)) (.lit (.nat 0))
    (.var 1)

def describe : State → String
  | .halted (.value (.data (.nat k))) => s!"halted with {k}"
  | .halted _ => "halted"
  | .running .. => "running"
  | .fault => "fault"

def bench (name : String) (t : Term) : IO Unit := do
  let code := compile t
  let t0 ← IO.monoMsNow
  let (steps, final) := runCount (load code)
  let t1 ← IO.monoMsNow
  let ms := t1 - t0
  let rate := if ms == 0 then 0 else steps * 1000 / ms
  IO.println s!"{name}: {steps} steps in {ms} ms, {rate} steps/s, {describe final}"

def main : IO Unit := do
  bench "countdown 1000000, direct" (countdown 1000000)
  bench "countdown 20000, interpreted" (level 1 (countdown 20000))
  bench "countdown 300, interpreted twice" (level 2 (countdown 300))
  bench "case walk over a text of 100000 characters" (caseWalk 100000)
  bench "codes, then a walk over its array, 100000 characters" (codesWalk 100000)
  bench "codes alone, 100000 characters" (codesOnly 100000)
