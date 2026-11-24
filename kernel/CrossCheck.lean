import Surface.Cross
import Surface.Read
import Reflect.Arith

/-! Two guests in one process (`Surface.Cross.simulate`), their records, and
    the check. Then records that were tampered with: each is refused, with the
    reason of the check that catches it. Every line starts `ok` or `FAIL`. -/

open Reflect Surface Surface.Cross

def bytesOf (path : String) : IO ByteArray := do
  let src ← IO.FS.readFile path
  match Surface.read src.toUTF8 with
  | .ok t => pure (Wire.programBytes t)
  | .error e => throw (IO.userError e)

def has (text part : String) : Bool := (text.splitOn part).length > 1

def expect (what text part : String) : IO Unit :=
  if has text part then IO.println s!"ok   {what}"
  else IO.println s!"FAIL {what}: wanted `{part}` in: {text}"

def records (path : String) (far takeNew : Bool) : IO (ByteArray × String × String) := do
  let p ← bytesOf path
  let (a, b) := simulated p 100000 40 far takeNew
  pure (p, a, b)

def accepted (what path : String) (far takeNew : Bool) (parts : List String) : IO Unit := do
  let (p, a, b) ← records path far takeNew
  let got := check p a.toUTF8 b.toUTF8
  for part in "accepted\n" :: parts do expect s!"{what}: {part.trimAscii}" got part

/-- The lines of a record, with its entry lines changed by `f`. -/
def entries (f : List String → List String) (record : String) : String :=
  let ls := (record.splitOn "\n").filter (· != "")
  let es := ls.filter (·.startsWith "entry ")
  let before := ls.takeWhile (fun l => !l.startsWith "entry " && !l.startsWith "head ")
  let after := ls.filter (fun l => l.startsWith "head " || l.startsWith "proc ")
  String.intercalate "\n" (before ++ f es ++ after) ++ "\n"

def swap (i j : Nat) (es : List String) : List String :=
  match es[i]?, es[j]? with
  | some x, some y => (es.set i y).set j x
  | _, _ => es

def drop (i : Nat) (es : List String) : List String := es.eraseIdx i

def twice (i : Nat) (es : List String) : List String :=
  match es[i]? with
  | some x => es.take (i + 1) ++ [x] ++ es.drop (i + 1)
  | none => es

def lie (record : String) : String := reseal record.toUTF8

def replace (record old new : String) : String := String.intercalate new (record.splitOn old)

def main : IO Unit := do
  let race := "../examples/cross-race.hom"
  -- Delivery order is recorded, and each order replays to its own result.
  accepted "race, oldest taken first" race true false
    ["schedule: [[0, 0, 0], [1, 0], [1, 0], [2, 1, 0], [2, 2, 0]]", "process 0: [1, 2]; holds [#0]"]
  accepted "race, newest taken first" race true true
    ["schedule: [[0, 0, 0], [1, 0], [1, 0], [2, 2, 0], [2, 1, 0]]", "process 0: [2, 1]; holds [#0]"]
  accepted "a function crosses and keeps running" "../examples/cross-reply.hom" true false
    ["process 0: [20, 22]; holds [#0]", "process 1: 7; holds [#0]", "process 2: 9; holds [#0]",
     "places b: [1, 2]"]
  accepted "a name crosses in a message" "../examples/cross-name.hom" true false
    ["process 0: 5; holds [#2, #0]", "process 1: []; holds [#2, #0]"]
  accepted "a send put out is held from a local receiver" "../examples/cross-held.hom" true false
    ["process 0: 1; holds [#0]", "process 1: []; holds [#0]", "process 2: waiting on [2, #0]; holds [#0]"]
  accepted "nothing crosses" "../examples/race.hom" false false
    ["schedule: [[0, 0, 0], [1, 0], [1, 0], [2, 0, 1]]", "places b: []"]
  accepted "a start stays near and its send finds a local receiver" race false false
    ["places a: [0, 1, 2]", "process 0: [1, 2]; holds [#0]"]
  let (p, a, b) ← records race true false
  let (_, a', b') ← records race true true
  let chk := fun (x y : String) => check p x.toUTF8 y.toUTF8
  if a == a' then IO.println "FAIL the two orders gave one record" else IO.println "ok   the two orders gave two records"
  -- The taker's log holds the order. The other guest's acknowledgements say
  -- only that each crossing was taken, so its record of the other run combines.
  expect "the acknowledgements in another order still combine" (chk a b') "process 0: [1, 2]; holds [#0]"
  expect "and so with the takings the other way" (chk a' b) "process 0: [2, 1]; holds [#0]"
  -- The chain as recorded.
  expect "an entry moved" (chk (entries (swap 5 6) a) b) "refused: log a: entry 5 does not name the entry before it"
  expect "an entry dropped" (chk a (entries (drop 2) b)) "refused: log b: entry 2 does not name the entry before it"
  expect "an entry repeated" (chk (entries (twice 5) a) b) "refused: log a: entry 6 does not name the entry before it"
  expect "the last entry dropped" (chk (entries (drop 6) a) b) "refused: log a: the head is not its last entry"
  expect "a mark with no order"
    (chk (replace a "entry [[0, [], 0], " "entry [[0, []], ") b) "refused: log a: entry 0 has no link"
  expect "an order that is not the place"
    (chk (replace a "entry [[0, [], 0], " "entry [[0, [], 1], ") b) "refused: log a: entry 0 is out of order"
  -- The chain made again, as a guest that lies would.
  expect "a resealed record is read" (chk (lie a) (lie b)) "accepted\n"
  expect "a taking repeated" (chk (lie (entries (twice 5) a)) b) "refused: the logs do not combine"
  expect "a taking dropped" (chk (lie (entries (drop 6) a)) b) "refused: the logs do not combine"
  expect "an acknowledgement dropped" (chk a (lie (entries (drop 5) b))) "refused: the logs do not combine"
  expect "a putting-out dropped" (chk a (lie (entries (drop 3) b))) "refused: the logs do not combine"
  expect "a crossing number that is not the count"
    (chk a (lie (replace b ", [1, 0, 0]]" ", [1, 0, 5]]"))) "refused: the logs do not combine"
  expect "an entry that names a held process"
    (chk (lie (entries (fun es => es.take 2 ++ ["entry [0, [0, [0, 0, 4]]]"] ++ es.drop 2) a)) b)
    "refused: the logs do not combine"
  expect "a local event repeated" (chk (lie (entries (twice 0) a)) b) "refused: [0, 0, 0] cannot happen"
  expect "the takings in another order"
    (chk (lie (entries (swap 5 6) a)) b) "refused: process 0 (a 0): reported [1, 2]; holds [#0], replayed [2, 1]; holds [#0]"
  expect "a name not handed over"
    (chk a (replace b "proc 1; holds [#0]" "proc 1; holds [#0, #2]")) "refused: process 1 (b 0): reported 1; holds [#0, #2], replayed 1; holds [#0]"
  expect "a process not reported" (chk a (replace b "proc 2; holds [#0]\n" "")) "refused: record b reports 0 more processes and its log 1 more"
  expect "another peer" (chk a (replace b "peer a" "peer c")) "refused: the records do not name each other"
  expect "another budget" (chk a (replace b "budget 100000" "budget 99999")) "refused: the budgets differ"
  let (q, _, _) ← records "../examples/cross-name.hom" true false
  expect "another program" (check q a.toUTF8 b.toUTF8) "refused: "
  -- A budget too small for a turn: nothing is put out, and the record still replays.
  let (s, t) := simulated p 30 40 true false
  expect "a budget that stops the first turn: nothing is recorded"
    (check p s.toUTF8 t.toUTF8) "accepted\nschedule: []\nplaces a: [0]\nplaces b: []\nprocess 0: waiting on [0]; holds []"

#eval main
