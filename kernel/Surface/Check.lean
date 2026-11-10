import Surface.Expect
import Surface.Run

/-!
Run with `lake env lean Surface/Check.lean` from `kernel/`. Checks every entry
of `reads`, `refused`, `prints`, and `renders`, and that rendered data reads
back as a program with the same data as its outcome. Prints each failing entry
and throws, so `lean` exits non-zero, if any check fails.
-/
open Reflect Surface

namespace Surface.Check

def hasWord (msg word : String) : Bool := (msg.splitOn word).length > 1

def show1 (s : String) : String := (s.replace "\n" "\\n")

/-- The data a program's machine run halts with, if it does. -/
def dataOf (src : String) (budget : Nat) : Option Data :=
  match read src.toUTF8 with
  | .error _ => none
  | .ok t =>
    match run budget (load (compile t)) with
    | .halted (.value (.data d)) => some d
    | _ => none

/-- Data that renders must read back, as a program, to that same data. -/
def roundTrip (d : Data) : Bool :=
  match dataOf (renderData d) 1000000 with
  | some d' => d' == d
  | none => false

def extraData : List Data := [
  .nat 0, .nat 18446744073709551616, .arr [], .arr [.arr []], .arr [.nat 1, .arr [.nat 2, .arr []], .nat 3],
  .arr [.arr [.arr [.nat 7]], .arr [], .nat 0]]

def main : IO UInt32 := do
  let mut fails := 0
  let mut total := 0
  for (text, t) in reads do
    total := total + 1
    match read text.toUTF8 with
    | .error m =>
      IO.println s!"FAIL reads {show1 text}: refused: {m}"
      fails := fails + 1
    | .ok got =>
      if reify got != reify t then
        IO.println s!"FAIL reads {show1 text}: wrong term\n  got      {repr got}\n  expected {repr t}"
        fails := fails + 1
  for (text, word) in refused do
    total := total + 1
    match read text.toUTF8 with
    | .ok got =>
      IO.println s!"FAIL refused {show1 text}: read as {repr got}"
      fails := fails + 1
    | .error m =>
      if !hasWord m word then
        IO.println s!"FAIL refused {show1 text}: message `{m}` lacks `{word}`"
        fails := fails + 1
  for (text, budget, out) in prints do
    total := total + 1
    let got := runText text.toUTF8 budget
    if got != out then
      IO.println s!"FAIL prints {show1 text}: printed `{got}`, expected `{out}`"
      fails := fails + 1
    -- A printed array or number must read back as a program with the same data.
    match dataOf text budget with
    | none => pure ()
    | some d =>
      total := total + 1
      if !roundTrip d then
        IO.println s!"FAIL roundtrip {show1 text}: `{renderData d}` does not read back"
        fails := fails + 1
  for (t, budget, out) in runs do
    total := total + 1
    let got := renderState budget (runUntil budget (load (compile t)))
    if got != out then
      fails := fails + 1
      IO.println s!"FAIL runs: `{got}`, expected `{out}`"
  for (o, out) in renders do
    total := total + 1
    let got := render o
    if got != out then
      IO.println s!"FAIL renders {repr o}: `{got}`, expected `{out}`"
      fails := fails + 1
    match o with
    | .value (.data d) =>
      total := total + 1
      if !roundTrip d then
        IO.println s!"FAIL roundtrip {repr d}: `{renderData d}` does not read back"
        fails := fails + 1
    | _ => pure ()
  for d in extraData do
    total := total + 1
    if !roundTrip d then
      IO.println s!"FAIL roundtrip {repr d}: `{renderData d}` does not read back"
      fails := fails + 1
  -- A syntax error is rendered with the prefix and a line and column.
  total := total + 1
  let e := runText "f 1".toUTF8 1000
  if !(e.startsWith "syntax error: line 1, column 1:") then
    IO.println s!"FAIL syntax error rendering: `{e}`"
    fails := fails + 1
  IO.println s!"{total - fails} of {total} checks passed"
  if fails > 0 then
    throw (IO.userError s!"{fails} check(s) failed")
  return 0

end Surface.Check

#eval Surface.Check.main
