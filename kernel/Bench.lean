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
