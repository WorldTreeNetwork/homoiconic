import Reflect.Arith
import Surface.Expect
import Surface.Run
import Surface.Bytes
import Surface.Chan
import Reflect.MachineSpace

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
    let got := renderState budget (runPriced budget (load (compile t)))
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
  -- `forever.hom` reads to the term `Reflect.MachineSpace` proves cycles, and
  -- a tail loop keeps no frame per call at any interpreter level: after two
  -- million steps the stack and frames are as shallow as after a few hundred
  -- (`homoiconic-q59.65`; with a frame per tail call level 0 holds 222222).
  total := total + 2
  let forever ← IO.FS.readBinFile "../examples/forever.hom"
  match read forever with
  | .error _ =>
    IO.println "FAIL forever.hom does not read"
    fails := fails + 2
  | .ok t =>
    if reify t != reify loopForever then
      IO.println "FAIL forever.hom does not read to Reflect.loopForever"
      fails := fails + 1
    let depths := [0, 1, 2].map fun k => depth (runPriced 2000000 (load (compile (level k t))))
    if depths.any (· > 64) then
      IO.println s!"FAIL forever.hom keeps frames: depth after 2000000 steps at levels 0, 1, 2 is {depths}"
      fails := fails + 1
  -- A syntax error is rendered with the prefix and a line and column.
  total := total + 1
  let e := runText "f 1".toUTF8 1000
  if !(e.startsWith "syntax error: line 1, column 1:") then
    IO.println s!"FAIL syntax error rendering: `{e}`"
    fails := fails + 1
  -- More than `maxLevels` levels are refused before the program is read, from
  -- source and from bytes; `maxLevels` levels run.
  total := total + 1
  if interpText "1".toUTF8 (maxLevels + 1) 1000 != levelsError
      || interpBytes ByteArray.empty (2 ^ 32 - 1) 1000 != levelsError
      || interpText "1".toUTF8 maxLevels 1000 == levelsError then
    IO.println s!"FAIL levels: more than {maxLevels} levels are not refused, or {maxLevels} are"
    fails := fails + 1
  -- A space limit beside the budget (`add-space-budget`). With no count a run
  -- has its ledger alone, so these outcomes depend on nothing outside Lean.
  let deep := "def deep x = [x, ...deep x]\ndeep 0\n"
  let build := "def build acc = build [0, ...acc]\nbuild []\n"
  let double := "def dbl x n =\n  case n\n    0 -> x\n    m + 1 -> dbl [x, ...x] m\n\ndbl [0] 40\n"
  let spaced : List (String × String × Nat × Nat × Nat × String) := [
    ("a recursion that waits", deep, 0, 10000000, 100000, "no result within 100000 cells"),
    ("a recursion that waits, through one interpreter", deep, 1, 10000000, 100000,
      "no result within 100000 cells"),
    ("a loop that builds", build, 0, 10000000, 100000, "no result within 100000 cells"),
    -- A tail loop keeps nothing, and a ledger alone still stops it: it makes
    -- more than a cell a step. Taking back what was dropped needs a count.
    ("a tail loop under a ledger alone", "def loop x = loop x\nloop 0\n", 0, 10000000, 100000,
      "no result within 100000 cells"),
    ("a tail loop out of steps first", "def loop x = loop x\nloop 0\n", 0, 5000, 100000,
      "no result within 5000 steps"),
    -- Forty cells that are 2^40 written: refused before anything is written.
    ("an answer built by doubling", double, 0, 1000000, 4000000, "no result within 4000000 cells"),
    ("an answer built by doubling, through one interpreter", double, 1, 10000000, 4000000,
      "no result within 4000000 cells"),
    ("factorial inside its ledger", "def f n =\n  case n\n    0 -> 1\n    m + 1 -> mul n (f m)\n\nf 30\n",
      1, 10000000, 4000000, "265252859812191058636308480000000")]
  for (what, text, levels, budget, cells, out) in spaced do
    total := total + 1
    let got := interpText text.toUTF8 levels budget false (.ledger cells)
    if got != out then
      IO.println s!"FAIL space, {what}: printed `{show1 got}`, expected `{out}`"
      fails := fails + 1
  -- `writes` is `written`, and two for the value as an item, on each shape.
  let shapes : List Data := [.nat 0, .nat 9, .nat 1000000, .nat (2 ^ 200), .name 7, .text [],
    .text "héllo".toList, .arr [], .arr [.nat 0, .nat 0], .arr [.arr [], .text "a".toList, .arr [.arr [.nat 5]]]]
  for d in shapes do
    total := total + 1
    let w := d.written + 2
    if !(d.writes w) || d.writes (w - 1) || (renderData d).utf8ByteSize > d.written then
      IO.println s!"FAIL written: {renderData d} is counted {d.written}, written in {(renderData d).utf8ByteSize} bytes"
      fails := fails + 1
  -- Cells of data as a tree, and of a number past a machine word.
  total := total + 1
  if (Data.arr [.nat 0, .text "ab".toList, .arr []]).cells != 9 || natCells (2 ^ 63 - 1) != 1
      || natCells (2 ^ 63) != 4 || natCells (2 ^ 200) != 7 then
    IO.println "FAIL cells: an array of three items, or a large number, is miscounted"
    fails := fails + 1
  IO.println s!"{total - fails} of {total} checks passed"
  if fails > 0 then
    throw (IO.userError s!"{fails} check(s) failed")
  return 0

end Surface.Check

#eval Surface.Check.main
