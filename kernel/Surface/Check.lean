import Reflect.Arith
import Surface.Expect
import Surface.Run
import Surface.Bytes
import Surface.Chan

/-!
Run with `lake env lean Surface/Check.lean` from `kernel/`. Checks every entry
of `reads`, `refused`, `prints`, `converses`, `renders`, `asTexts`, `channels`
and `channelFiles`, that rendered data with no name in it reads back as a program
with the same data as its outcome, and that rendered data with a name in it
does not read. Prints each failing entry
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

mutual
  /-- Is there a name anywhere in the data? -/
  def hasName : Data → Bool
    | .name _ => true
    | .nat _ => false
    | .text _ => false
    | .arr xs => anyName xs
  def anyName : List Data → Bool
    | [] => false
    | x :: xs => hasName x || anyName xs
end

/-- Rendered data reads back; with a name in it, the reader refuses it. -/
def readsBack (d : Data) : Bool :=
  if hasName d then
    match read (renderData d).toUTF8 with
    | .error _ => true
    | .ok _ => false
  else roundTrip d

/-- No process holds a name twice, and none after process 2 holds name 0. -/
def sieveHeld (cfg : MConfig) : Bool :=
  cfg.procs.all (fun q => q.held.eraseDups.length == q.held.length) &&
    (cfg.procs.drop 3).all (fun q => !q.held.contains 0) && cfg.procs.length == 13

def extraData : List Data := [
  .nat 0, .nat 18446744073709551616, .arr [], .arr [.arr []], .arr [.nat 1, .arr [.nat 2, .arr []], .nat 3],
  .arr [.arr [.arr [.nat 7]], .arr [], .nat 0],
  .text [], .text "plain".toList, .text "\"\\\n\t' é →𐅑".toList,
  .arr [.nat 1, .text "a\"b".toList, .arr [.text [], .nat 34]],
  .text ((List.range 300).map fun i => Char.ofNat (32 + i))]

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
  for (text, answers, budget, out) in converses do
    total := total + 1
    let got := converseText text.toUTF8 answers.toUTF8 budget
    if got != out then
      IO.println s!"FAIL converses {show1 text} with {show1 answers}: printed `{show1 got}`, expected `{show1 out}`"
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
      if !readsBack d then
        IO.println s!"FAIL roundtrip {repr d}: `{renderData d}` does not read back, or holds a name and reads"
        fails := fails + 1
    | _ => pure ()
  for (text, levels, out) in asTexts do
    total := total + 1
    let got := interpText text.toUTF8 levels 10000000 true
    if got != out then
      IO.println s!"FAIL --text {show1 text} at level {levels}: wrote `{show1 got}`, expected `{show1 out}`"
      fails := fails + 1
  for (text, schedule, out) in channels do
    total := total + 1
    let got := channelsText text.toUTF8 schedule.toUTF8 1000000 100
    if got != out then
      IO.println s!"FAIL channels {show1 text} with `{schedule}`: printed `{show1 got}`, expected `{show1 out}`"
      fails := fails + 1
  for (file, scheduleFile, out) in channelFiles do
    total := total + 1
    let program ← IO.FS.readBinFile s!"../examples/{file}"
    let schedule ← if scheduleFile == "" then pure ByteArray.empty
      else IO.FS.readBinFile s!"../examples/{scheduleFile}"
    let got := channelsText program schedule 1000000 100
    if got != out then
      IO.println s!"FAIL channels {file} with `{scheduleFile}`: printed `{show1 got}`, expected `{show1 out}`"
      fails := fails + 1
  -- The sieve: its process lines, and the held lists themselves.
  total := total + 2
  let sieve ← IO.FS.readBinFile "../examples/sieve.hom"
  let sieveText := channelsText sieve ByteArray.empty 100000000 100000
  if (sieveText.splitOn "\n").filter (·.startsWith "process") != sieveProcesses.splitOn "\n" then
    IO.println s!"FAIL sieve: the process lines are\n{sieveText}"
    fails := fails + 1
  let held := match read sieve with
    | .error _ => false
    | .ok t =>
      match beginRun 100000000 t with
      | none => false
      | some c₀ => sieveHeld (autoRun 100000000 100000 c₀).2.1
  if !held then
    IO.println "FAIL sieve: a process holds a name twice, or a process after process 2 holds #0"
    fails := fails + 1
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
