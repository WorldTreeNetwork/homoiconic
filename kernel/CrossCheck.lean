import Surface.Cross
import Surface.Read
import Reflect.Arith

/-! Two guests in one process (`Surface.Cross.simulateWith`), their records, and
    the check. Then records that were tampered with: each is refused, with the
    reason of the check that catches it. Then the guests' own limits
    (`harden-crossing`): budgets, the hold, the caps, the queue, and what a
    record's lines carry. Every line starts `ok` or `FAIL`. -/

open Reflect Surface Surface.Cross

def bytesOf (path : String) : IO ByteArray := do
  let src ← IO.FS.readFile path
  match Surface.read src.toUTF8 with
  | .ok t => pure (Wire.programBytes t)
  | .error e => throw (IO.userError e)

def has (text part : String) : Bool := (text.splitOn part).length > 1

def expect (what text part : String) : IO Unit :=
  if has text part then IO.println s!"ok   {what}"
  else IO.println s!"FAIL {what}: wanted `{part}` in: {(text.take 3000).toString}"

def expectNot (what text part : String) : IO Unit :=
  if has text part then IO.println s!"FAIL {what}: did not want `{part}` in: {(text.take 3000).toString}"
  else IO.println s!"ok   {what}"

def truth (what : String) (b : Bool) (detail : String := "") : IO Unit :=
  if b then IO.println s!"ok   {what}" else IO.println s!"FAIL {what} {detail}"

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

/-- The record with every line that starts with `prefix` dropped. -/
def dropLines (prefix_ : String) (record : String) : String :=
  String.intercalate "\n" ((record.splitOn "\n").filter (fun l => !l.startsWith prefix_))

def swap (i j : Nat) (es : List String) : List String :=
  match es[i]?, es[j]? with
  | some x, some y => (es.set i y).set j x
  | _, _ => es

def drop (i : Nat) (es : List String) : List String := es.eraseIdx i

def twice (i : Nat) (es : List String) : List String :=
  match es[i]? with
  | some x => es.take (i + 1) ++ [x] ++ es.drop (i + 1)
  | none => es

def insertAt (i : Nat) (line : String) (es : List String) : List String :=
  es.take i ++ [line] ++ es.drop i

/-- The place of the first entry line whose body is `body`. -/
def entryWith (body : String) (record : String) : Nat :=
  ((record.splitOn "\n").filter (·.startsWith "entry ")).findIdx (fun l => has l (", " ++ body ++ "]"))

def lie (record : String) : String := reseal record.toUTF8

/-- Two guests run to the end in one process have closed with nothing in
    flight: neither keeps a packet the other has not counted, and neither has
    accepted a packet it has not worked. -/
def closedQuiet (path : String) (far takeNew : Bool) : IO Bool := do
  let p ← bytesOf path
  let ba := simulateWith p { frame := 100000, exchanges := 40, far, takeNew }
  pure (ba.1.closed && ba.2.closed && ba.1.sent.isEmpty && ba.2.sent.isEmpty &&
    ba.1.inbox.isEmpty && ba.2.inbox.isEmpty)

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
  -- The pairs above closed with nothing in flight. The theorems of
  -- `GuestContract.lean` speak of such pairs; that closing leaves a pair so is
  -- not proved (`homoiconic-q59.85`), and this is its test.
  let mut quiet := true
  for (path, far, takeNew) in [(race, true, false), (race, true, true),
      ("../examples/cross-reply.hom", true, false), ("../examples/cross-name.hom", true, false),
      ("../examples/cross-held.hom", true, false), ("../examples/race.hom", false, false),
      (race, false, false)] do
    if !(← closedQuiet path far takeNew) then quiet := false
  truth "the pairs above closed with nothing in flight" quiet
  let (p, a, b) ← records race true false
  let (_, a', b') ← records race true true
  let chk := fun (x y : String) => check p x.toUTF8 y.toUTF8
  if a == a' then IO.println "FAIL the two orders gave one record" else IO.println "ok   the two orders gave two records"
  expect "a record is of form 2 and says what it ran with and its own limits" a
    "form 2\nme a\npeer b\nbudget 100000 500000\nown 100000000 500000 2000000\n"
  expect "a line carries a root" a "proc [1, 2]; holds [#0]; root "
  -- The taker's log holds the order, and the other guest's acknowledgements
  -- follow it: a record of one order does not go with one of the other.
  expect "the acknowledgements in another order" (chk a b')
    "refused: the acknowledgements of b are not the order a took them in"
  expect "and so with the takings the other way" (chk a' b)
    "refused: the acknowledgements of b are not the order a took them in"
  -- The chain as recorded.
  expect "an entry moved" (chk (entries (swap 5 6) a) b) "refused: log a: entry 5 does not name the entry before it"
  expect "an entry dropped" (chk a (entries (drop 2) b)) "refused: log b: entry 2 does not name the entry before it"
  expect "an entry repeated" (chk (entries (twice 5) a) b) "refused: log a: entry 6 does not name the entry before it"
  expect "the last entry dropped" (chk (entries (drop 6) a) b) "refused: log a: the head is not its last entry"
  expect "a mark with no order"
    (chk (replace a "entry [[0, [], 0], " "entry [[0, []], ") b) "refused: log a: entry 0 has no link"
  expect "an order that is not the place"
    (chk (replace a "entry [[0, [], 0], " "entry [[0, [], 1], ") b) "refused: log a: entry 0 is out of order"
  expect "a record of the old form" (chk (dropLines "form " a) b) "refused: record a: not of form 2"
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
    (chk (lie (entries (swap 5 6) a)) b) "refused: the acknowledgements of b are not the order a took them in"
  expect "an answer from outside in a log"
    (chk (lie (entries (fun es => es ++ ["entry [0, [0, [3, 0, 5]]]"]) a)) b)
    "refused: an answer from outside in a crossing"
  expect "a name not handed over"
    (chk a (replace b "proc 1; holds [#0]" "proc 1; holds [#0, #2]"))
    "refused: process 1 (b 0): reported 1; holds [#0, #2]; root "
  expect "a process not reported" (chk a (dropLines "proc 2; holds [#0]" b))
    "refused: record b reports 0 more processes and its log 1 more"
  expect "another peer" (chk a (replace b "peer a" "peer c")) "refused: the records do not name each other"
  expect "another budget" (chk a (replace b "budget 100000 500000" "budget 99999 500000")) "refused: the budgets differ"
  expect "another turn space" (chk a (replace b "budget 100000 500000" "budget 100000 400000"))
    "refused: the budgets differ"
  expect "a budget above its own limits"
    (chk a (replace b "own 100000000 500000" "own 99999 500000")) "refused: record b: its budget is above its own limits"
  expect "a record that asks more than this check runs"
    (chk (replace (replace a "budget 100000 500000" "budget 100000 5000000") "own 100000000 500000" "own 100000000 5000000")
      (replace (replace b "budget 100000 500000" "budget 100000 5000000") "own 100000000 500000" "own 100000000 5000000"))
    "refused: the record asks more than this check runs"
  let (q, _, _) ← records "../examples/cross-name.hom" true false
  expect "another program" (check q a.toUTF8 b.toUTF8) "refused: "
  -- A budget too small for a turn: nothing is put out, and the record still replays.
  let (s, t) := simulated p 30 40 true false
  expect "a budget that stops the first turn: nothing is recorded"
    (check p s.toUTF8 t.toUTF8) "accepted\nschedule: []\nplaces a: [0]\nplaces b: []\nbudget 30 steps"

  -- Mid-run two honest logs need not combine (q59.68): `b` has taken `a`'s
  -- start and `a` has not yet worked the acknowledgement, so the crossing is
  -- taken and not acknowledged. `honest_combine` speaks of a pair with nothing
  -- in flight, and this one has the acknowledgement still to send.
  let ma₀ := (start true false true false defaultLimit defaultTurn defaultHold).give p 100000
  let mb₀ := start false true false false defaultLimit defaultTurn defaultHold
  let ma := (ma₀.take (mb₀.batch roomLimit)).work ledgerCount workLimit
  let mb := (mb₀.take (ma.batch roomLimit)).work ledgerCount workLimit
  expect "mid-run, a start taken and its acknowledgement not yet worked: the logs do not combine"
    (chk (ma.record "a" "b") (mb.record "b" "a")) "refused: the logs do not combine"
  truth "and the pair is not quiet: the acknowledgement is still to be sent"
    (ma.log.any (· == .out 0 0) && mb.log.any (· == .spawnIn 0) && mb.sent.any (· == ackPacket 0))

  -- Budgets are the guest's own (q59.79).
  let (fa, fb) := simulatedWith p { far := true, frame := 100000, limitB := 50000, turnB := 300000 }
  expect "the program comes with more than the peer allows: a runs with b's" fa "budget 50000 300000\n"
  expect "and b with its own" fb "budget 50000 300000\nown 50000 300000 2000000\n"
  expect "and the two replay" (chk fa fb) "accepted\n"
  let early := ((start true false false false defaultLimit defaultTurn defaultHold).give p 100000).work ledgerCount 100
  truth "the guest given the program does not begin before it hears the peer" early.cfg.procs.isEmpty
  -- A peer that announces a huge budget, before this guest has run anything.
  let startPkt : Data := .arr [.nat 0, .nat 0, reify (.lam (.var 0)), .nat 7, .arr []]
  let huge := 1000000000000000000
  let g₀ := start false true false false 100000 500000 defaultHold
  let g₁ := (g₀.take (Wire.write (.arr [.nat 0, .nat 0, .nat huge, .nat huge, .arr [.arr [.nat 0, startPkt]]]))).work ledgerCount workLimit
  expect "a peer announces a huge budget: the guest runs with its own" (g₁.record "b" "a") "budget 100000 500000\n"
  truth "and took the start" (g₁.cfg.procs.length == 1)
  let g₂ := g₁.take (Wire.write (.arr [.nat 0, .nat 1, .nat 1, .nat 1, .arr []]))
  truth "a lower budget after the guest ran is not taken" (g₂.budget == 100000 && g₂.cells == 500000)

  -- What a guest holds (q59.71).
  let grow ← bytesOf "../examples/cross-grow.hom"
  let (ga, gb) := simulatedWith grow { holdA := 200000 }
  let gc := check grow ga.toUTF8 gb.toUTF8
  expect "a process that holds more and more: accepted" gc "accepted\n"
  expect "and its guest is full" gc "full a: entry "
  let fan ← bytesOf "../examples/cross-fan.hom"
  let (na, nb) := simulatedWith fan { far := true, frame := 10000000, holdB := 200000, exchanges := 200 }
  let nc := check fan na.toUTF8 nb.toUTF8
  expect "processes started on the other guest that each hold a turn's worth: accepted" nc "accepted\n"
  expect "and the other guest is full" nc "full b: entry "
  expect "a payload longer than a line prints" na "waiting on more than 512 written"
  -- Counts: a count that is a fixed number, so the guest goes on.
  let (ca, cb) := simulatedWith p { far := true, holdA := 600, countA := fun _ => 100 }
  let cc := chk ca cb
  expect "counts recorded where the ledger was spent: accepted" cc "accepted\n"
  expectNot "and some counted" cc "hold a: 600 cells, 0 counts"
  let k := entryWith "[5, 100]" ca
  expect "a count dropped" (chk (lie (entries (drop k) ca)) cb)
    s!"refused: hold a: entry {k}: the ledger was spent and not counted"
  expect "a count where nothing was spent" (chk (lie (entries (insertAt (k + 1) "entry [0, [5, 100]]") ca)) cb)
    s!"refused: hold a: entry {k + 1}: a count where the ledger was not spent"
  expect "a count past the bar" (chk (lie (entries (fun es => es.set k "entry [0, [5, 599]]") ca)) cb)
    s!"refused: hold a: entry {k}: a count past the bar that is not full"
  expect "full within the bar" (chk (lie (entries (fun es => es.set k "entry [0, [6, 100]]") ca)) cb)
    s!"refused: hold a: entry {k}: full within the bar"
  let ge := ((ga.splitOn "\n").filter (·.startsWith "entry ")).length
  expect "an entry after full" (check grow (lie (entries (fun es => es ++ ["entry [0, [0, [0, 0, 1000]]]"]) ga)).toUTF8 gb.toUTF8)
    s!"refused: hold a: entry {ge}: an entry after full"
  -- The caps on a log, by the walk: an entry that reaches the cap is followed
  -- by `full`.
  let plain : List Charged := (List.range entryLimit).map fun _ => ⟨.did (.fresh 0 0), 0, 1⟩
  truth "a log at its cap followed by full is accepted"
    (match holdWalk 1000 0 (plain ++ [⟨.full 0, 0, 1⟩]) with | .ok (some _) => true | _ => false)
  truth "a log at its cap and not full is refused"
    (match holdWalk 1000 0 (plain ++ [⟨.did (.fresh 0 0), 0, 1⟩]) with
     | .error (_, w) => w == "the ledger was spent and not counted" | _ => false)
  truth "a log at its cap with a count that is not full is refused"
    (match holdWalk 1000 0 (plain ++ [⟨.held 0, 0, 1⟩]) with
     | .error (_, w) => w == "a cap reached and not full" | _ => false)
  -- What the peer can make a guest hold.
  let sendPkt (k : Nat) : Data := .arr [.nat 1, .nat k, .nat 9, .nat k, .arr []]
  let flood := (List.range 200).map fun k => Data.arr [.nat k, sendPkt k]
  let q₁ := g₀.take (Wire.write (.arr [.nat 0, .nat 0, .nat 1, .nat 1, .arr flood]))
  truth "a batch of 200 packets: 128 are accepted" (q₁.got == 128) s!"got {q₁.got}"
  let starts (from_ : Nat) := (List.range 64).map fun d => Data.arr [.nat (from_ + d), .arr [.nat 0, .nat (from_ + d), reify (.lam (.var 0)), .nat 7, .arr []]]
  let feed (g : Guest) (from_ : Nat) : Guest :=
    (g.take (Wire.write (.arr [.nat 0, .nat 0, .nat 100000, .nat 500000, .arr (starts from_)]))).work ledgerCount 1000
  let s₃ := feed (feed (feed g₀ 0) 64) 128
  truth "a peer that never counts: the guest stops at 128 packets" (s₃.sent.length == 128) s!"sent {s₃.sent.length}"
  let many ← bytesOf "../examples/cross-many.hom"
  let m₀ := ((start true false false false defaultLimit defaultTurn defaultHold).give many 100000).take
    (Wire.write (.arr [.nat 0, .nat 0, .nat 100000, .nat 500000, .arr []]))
  let m₁ := m₀.work ledgerCount 1000
  truth "seventy sends for a peer that takes none: 64 are put out" (m₁.asked.length == 64) s!"asked {m₁.asked.length}"

  -- What the check compares (q59.69).
  let wide ← bytesOf "../examples/cross-wide.hom"
  let (wa, wb) := simulatedWith wide {}
  expect "a function whose form does not fit: the line has the data digest" wa "; holds [#0]; data "
  expect "and it is checked" (check wide wa.toUTF8 wb.toUTF8) "accepted\n"
  let hidden ← bytesOf "../examples/cross-hidden.hom"
  let (ha, hb) := simulatedWith hidden {}
  expect "a race kept out of sight: accepted" (check hidden ha.toUTF8 hb.toUTF8) "accepted\n"
  expect "a different run of the same program, its state as it was, re-signed"
    (check hidden (lie (entries (swap 3 4) ha)).toUTF8 hb.toUTF8)
    "refused: process 0 (a 0): reported waiting on [2, #0]; holds [#0]; root "
  let whole := remake hidden (lie (entries (swap 3 4) ha)).toUTF8 hb.toUTF8 true
  expect "the same, made whole with that run's lines: accepted, as a lying guest can"
    (check hidden whole.toUTF8 hb.toUTF8) "accepted\n"

#eval main
