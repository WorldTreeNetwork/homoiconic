import Reflect.Arith
import Reflect
import Wire
import Surface
open Reflect Wire Surface.Keep

/-! Tests the node session (`Surface.Keep.nodeStart`, `nodeFrom`) against the
    proved `Reflect.nodeRun`: the node the session saves has the root that
    `nodeRun`'s node has when it is saved the same way, whether the session
    began at the program or at a kept node. Each line that starts with FAIL
    fails the check. -/

def line (ok : Bool) (what : String) : String := s!"{if ok then "ok  " else "FAIL"} {what}"

abbrev Pieces := Std.HashMap Ref ByteArray

def finish (m : Pieces) : Nat → Session → String × Pieces
  | 0, _ => ("did not finish", m)
  | fuel + 1, s =>
      match s.need with
      | some r =>
          match m[r]? with
          | some b => finish m fuel (give s b)
          | none => ("lacks a piece", m)
      | none => (s.text, s.written.foldl (fun m rb => m.insert rb.1 rb.2) m)

def part (start : String) (text : String) : String :=
  ((text.splitOn "\n").find? (·.startsWith start)).getD ""

def opsText (os : List Op) : ByteArray :=
  (Surface.renderData (.arr (os.map fun o => .arr [o.id, Surface.eventData o.event]))).toUTF8

def budget : Nat := 100000000

/-- The node `nodeRun` reaches, saved as the session saves a node. -/
def provedState (t : Term) (os : List Op) : String :=
  match beginRun budget t with
  | none => "unfinished"
  | some c₀ =>
      -- The ops here are written as a mark and an event; the session seals
      -- each as it reads the log, so `nodeRun` is given the same seals.
      let os := os.map fun (o : Op) =>
        Op.seal entryName o.id (Surface.eventData o.event) o.event
      let n := (nodeRun budget ⟨c₀, []⟩ os).2.1
      let status : Status MValue MOutcome → Option (P Ref)
        | .waiting c p => some (plist [.nat 0, c.toP, p.toP])
        | .finished (.value (.data d)) => some (plist [.nat 1, d.toP])
        | .finished (.unbound i) => some (plist [.nat 2, .nat i])
        | .finished .wrong => some (plist [.nat 3])
        | _ => none
      match n.cfg.procs.mapM fun q =>
          (status q.status).map fun st => plist [Data.toP (.arr (q.held.map .nat)), st] with
      | none => "no state"
      | some procs =>
          match save pieceSize (plist [Data.toP (.arr n.seen),
              Data.toP (.arr (n.cfg.names.map .nat)), plist procs]) with
          | some (root, _) => "state: " ++ hex root
          | none => "no state"

/-- A log for a program: the events the chooser picks, numbered from 1. -/
def chosen (t : Term) : List Op :=
  match beginRun budget t with
  | none => []
  | some c₀ =>
      let evs := (autoRun budget 50 c₀).1
      (List.range evs.length).zip evs |>.map fun (k, ev) => ⟨.nat (k + 1), ev⟩

#eval do
  for name in ["ping", "race", "guess", "number"] do
    let src ← IO.FS.readFile s!"../examples/{name}.hom"
    match Surface.read src.toUTF8 with
    | .error _ => IO.println (line false s!"{name}: does not read")
    | .ok t =>
      let log := chosen t
      let start (os : List Op) : String × Pieces :=
        finish {} 100000 (nodeStart src.toUTF8 (opsText os) budget)
      let state (os : List Op) : String := part "state: " (start os).1
      -- From the start, the session and `nodeRun` agree after every prefix.
      let agree := (List.range (log.length + 1)).all fun k =>
        state (log.take k) == provedState t (log.take k) && (state (log.take k)).length == 71
      IO.println (line (agree && log.length ≥ 2)
        s!"{name}: the session and nodeRun agree after each of {log.length + 1} prefixes")
      -- A node kept at each prefix, given the whole log, reaches the whole
      -- log's node.
      let restarted := (List.range (log.length + 1)).all fun k =>
        let (text, m) := start (log.take k)
        let root := ((part "state: " text).drop 7).toString
        part "state: " (finish m 100000 (nodeFrom root (opsText log) budget)).1 == state log
      IO.println (line restarted
        s!"{name}: a node kept at any prefix and given the whole log reaches the same node")
      -- Ops delivered again change nothing.
      IO.println (line (state (log ++ log.take 2 ++ log) == state log)
        s!"{name}: repeats leave the node as it is")
      -- An op that cannot happen: the node is saved as it stood.
      let bad : Op := ⟨.nat 999, .comm 7 8⟩
      let (text, _) := start (log.take 1 ++ [bad] ++ log.drop 1)
      IO.println (line (part "state: " text == state (log.take 1) &&
          part "refused: " text == "refused: entry 1, [2, 7, 8], cannot happen")
        s!"{name}: {part "refused: " text}")

/-- A piece saved as the session saves a node, in a store of its own. -/
def keptPiece (state : P Ref) : String × Pieces :=
  match save pieceSize state with
  | some (root, pieces) => (hex root, pieces.foldl (fun m rb => m.insert rb.1 rb.2) {})
  | none => ("", {})

-- Pieces that hash to their names and are not nodes are refused.
#eval do
  let done : P Ref := plist [.nil, plist [.nat 1, .nat 42]]
  let function : P Ref := .closure (compile (.lit (.nat 42))) .nil
  let bad : List (String × P Ref) :=
    [ ("a fourth part", plist [.nil, .nil, plist [done], .nat 9]),
      ("a VM state", plist [.nil, plist [.nat 1, .nat 42]]),
      ("a process with a third part", plist [.nil, .nil, plist [plist [.nil, plist [.nat 1, .nat 42], .nat 9]]]),
      ("a name that is not a number", plist [.nil, plist [.nil], plist [done]]),
      ("a held name that is not a number", plist [.nil, .nil, plist [plist [plist [.nil], plist [.nat 1, .nat 42]]]]),
      ("a waiting program that is not a function", plist [.nil, .nil, plist [plist [.nil, plist [.nat 0, .nat 3, .nat 4]]]]),
      ("a waiting program with no payload", plist [.nil, .nil, plist [plist [.nil, plist [.nat 0, function]]]]),
      ("a payload that holds a function", plist [.nil, .nil, plist [plist [.nil, plist [.nat 0, function, function]]]]),
      ("a process list that does not end", plist [.nil, .nil, .cons done (.nat 5)]) ]
  for (what, piece) in bad do
    let (root, m) := keptPiece piece
    let (text, _) := finish m 1000 (nodeFrom root "[]".toUTF8 1000000)
    IO.println (line (text.startsWith "store error: the root is not a kept node")
      s!"refused: {what}")
  let (root, m) := keptPiece (plist [.nil, .nil, plist [done]])
  let (text, _) := finish m 1000 (nodeFrom root "[]".toUTF8 1000000)
  IO.println (line (text.startsWith "process 0: 42; holds []\n") "a node of that shape is accepted")

/-! A logged node and a name. The log makes two channels (fresh), starts a
    second process on the first, and hands it the second name in a message
    (transfer), then hands it both names again in another message. -/

def handoffText : String :=
"let child = quote (fn meet ->
  ask [2, meet] (fn a ->
    ask [2, meet] (fn b ->
      ask [1, a, 5] (fn sent -> [a, b]))))
ask [0] (fn meet ->
  ask [3, child, meet] (fn started ->
    ask [0] (fn line ->
      ask [1, meet, line] (fn first ->
        ask [1, meet, [line, meet]] (fn second ->
          ask [2, line] (fn reply -> reply))))))"

def handoffLog : List Op :=
  [⟨.nat 1, .fresh 0 0⟩, ⟨.nat 2, .spawn 0⟩, ⟨.nat 3, .fresh 0 1⟩,
   ⟨.nat 4, .comm 0 1⟩, ⟨.nat 5, .comm 0 1⟩, ⟨.nat 6, .comm 1 0⟩]

/-- A stored piece and everything under it, with no reference left. -/
partial def whole (m : Pieces) : P Ref → Option (P Ref)
  | .nat n => some (.nat n)
  | .name n => some (.name n)
  | .text t => some (.text t)
  | .nil => some .nil
  | .cons h t => do
      let h' ← whole m h
      let t' ← whole m t
      pure (.cons h' t')
  | .closure c e => do
      let e' ← whole m e
      pure (.closure c e')
  | .ref r => do
      let b ← m[r]?
      match readPiece b with
      | .ok p => whole m p
      | .error _ => none

def items : P Ref → List (P Ref)
  | .cons h t => h :: items t
  | _ => []

/-- The kept node at `root`: the names made, each process's held names, and
    the hex of its whole byte form. -/
def keptNode (m : Pieces) (root : String) : Option (Option Data × List (Option Data) × String) := do
  let r ← unhex root
  let node ← whole m (.ref r)
  match items node with
  | [_, names, procs] =>
      let helds := (items procs).map fun q => ((items q).head?).bind P.toData
      pure (names.toData, helds, (pieceBytes node).elim "" hex)
  | _ => none

def contains (text word : String) : Bool := (text.splitOn word).length > 1

#eval do
  match Surface.read handoffText.toUTF8 with
  | .error _ => IO.println (line false "handoff: does not read")
  | .ok t =>
    let log := handoffLog
    let start (os : List Op) : String × Pieces :=
      finish {} 100000 (nodeStart handoffText.toUTF8 (opsText os) budget)
    let state (os : List Op) : String := part "state: " (start os).1
    -- The log is the one the chooser picks.
    let picked := Surface.renderData (.arr ((chosen t).map fun (o : Op) => Surface.eventData o.event))
    IO.println (line (picked == "[[0, 0, 0], [1, 0], [0, 0, 1], [2, 0, 1], [2, 0, 1], [2, 1, 0]]"
        && picked == Surface.renderData (.arr (log.map fun (o : Op) => Surface.eventData o.event)))
      "handoff: the log is the events the chooser picks")
    -- The session and `nodeRun` agree after every prefix.
    let agree := (List.range (log.length + 1)).all fun k =>
      state (log.take k) == provedState t (log.take k) && (state (log.take k)).length == 71
    IO.println (line agree
      s!"handoff: the session and nodeRun agree after each of {log.length + 1} prefixes")
    -- Each op delivered a second time, straight after itself and at the end,
    -- changes nothing: the same root, and one op more given than acted on.
    let again := (List.range log.length).all fun k =>
      let twice := log.take (k + 1) ++ (log.drop k).take 1 ++ log.drop (k + 1)
      let late := log ++ (log.drop k).take 1
      state twice == state log && state late == state log &&
        provedState t twice == state log &&
        part "entries: " (start twice).1 == "entries: 7 given, 6 acted on" &&
        -- Part way too: the duplicate of op k, given with the first k + 1 ops.
        state (log.take (k + 1) ++ (log.drop k).take 1) == state (log.take (k + 1))
    IO.println (line again "handoff: an op delivered a second time changes nothing")
    -- The receiver was handed `#1` twice and `#0` twice, and holds each once.
    let (text, m) := start log
    let lines := (text.splitOn "\n").take 2
    IO.println (line (lines == ["process 0: 5; holds [#1, #0]", "process 1: [#1, [#1, #0]]; holds [#1, #0]"])
      s!"handoff: the receiver holds each name once: {lines}")
    let proved := match beginRun budget t with
      | some c₀ => (nodeRun budget ⟨c₀, []⟩ log).2.1.cfg.procs.map fun (q : Proc MValue MOutcome) => q.held
      | none => []
    IO.println (line (proved == [[1, 0], [1, 0]]) s!"handoff: nodeRun's processes hold {proved}")
    -- From every saved prefix, the rest of the log reaches the same root, and
    -- so does the whole log given again.
    let restarted := (List.range (log.length + 1)).all fun k =>
      let (text, m) := start (log.take k)
      let root := ((part "state: " text).drop 7).toString
      part "state: " (finish m 100000 (nodeFrom root (opsText (log.drop k)) budget)).1 == state log &&
        part "state: " (finish m 100000 (nodeFrom root (opsText log) budget)).1 == state log
    IO.println (line restarted
      "handoff: a node saved at any prefix and given the rest of the log reaches the same root")
    -- What is saved: the names made and the names held are plain numbers; a
    -- name value in a result is the name, under tag 39.
    let nums (ns : List Nat) : Option Data := some (.arr (ns.map .nat))
    let saved := match keptNode m ((part "state: " text).drop 7).toString with
      | some (names, helds, bytes) =>
          names == nums [1, 0] && helds == [nums [1, 0], nums [1, 0]] &&
            contains bytes "d82701" && contains bytes "d82700"
      | none => false
    IO.println (line saved
      "handoff: the saved node holds its names as numbers and the name values under tag 39")
    -- Part way, after the first transfer: the receiver waits with `#1` in its
    -- function, holding `[1, 0]`; the sender waits on a payload of two names.
    let (mid, mm) := start (log.take 4)
    let midSaved := match keptNode mm ((part "state: " mid).drop 7).toString with
      | some (names, helds, bytes) =>
          names == nums [1, 0] && helds == [nums [1, 0], nums [1, 0]] && contains bytes "d82701"
      | none => false
    IO.println (line (midSaved &&
        (mid.splitOn "\n").take 2 == ["process 0: waiting on [1, #0, [#1, #0]]; holds [#1, #0]",
          "process 1: waiting on [2, #0]; holds [#1, #0]"])
      s!"handoff: saved part way, {(mid.splitOn "\n").take 2}")

-- A kept node whose held list or names list holds a name value is not a node:
-- those lists are numbers.
#eval do
  let done : P Ref := plist [.nil, plist [.nat 1, .nat 42]]
  let bad : List (String × P Ref) :=
    [ ("a name made that is a name value", plist [.nil, plist [.name 0], plist [done]]),
      ("a held name that is a name value",
        plist [.nil, plist [.nat 0], plist [plist [plist [.name 0], plist [.nat 1, .nat 42]]]]) ]
  for (what, piece) in bad do
    let (root, m) := keptPiece piece
    let (text, _) := finish m 1000 (nodeFrom root "[]".toUTF8 1000000)
    IO.println (line (text.startsWith "store error: the root is not a kept node")
      s!"refused: {what}")
  -- A result that is a name value is kept and printed as a name.
  let (root, m) := keptPiece (plist [.nil, plist [.nat 0], plist [plist [plist [.nat 0], plist [.nat 1, .name 0]]]])
  let (text, _) := finish m 1000 (nodeFrom root "[]".toUTF8 1000000)
  IO.println (line (text.startsWith "process 0: #0; holds [#0]\n") "a kept result that is a name is a name")

-- The sieve as a logged node: the session and `nodeRun` agree on the whole
-- log; no process holds a name twice; no process after process 2 holds name 0,
-- which only the first three were given.
#eval do
  let src ← IO.FS.readFile "../examples/sieve.hom"
  match Surface.read src.toUTF8 with
  | .error _ => IO.println (line false "sieve: does not read")
  | .ok t =>
    match beginRun budget t with
    | none => IO.println (line false "sieve: does not begin")
    | some c₀ =>
      let evs := (autoRun budget 100000 c₀).1
      let log : List Op := (List.range evs.length).zip evs |>.map fun (k, ev) => ⟨.nat (k + 1), ev⟩
      let (text, _) := finish {} 1000000 (nodeStart src.toUTF8 (opsText log) budget)
      IO.println (line (part "state: " text == provedState t log && (part "state: " text).length == 71)
        s!"sieve: the session and nodeRun agree on the whole log of {log.length} ops")
      let helds := (nodeRun budget ⟨c₀, []⟩ log).2.1.cfg.procs.map fun (q : Proc MValue MOutcome) => q.held
      let once := helds.all fun h => h.eraseDups.length == h.length
      let kept := (helds.drop 3).all fun h => !h.contains 0
      IO.println (line (once && kept && helds.length == 13 && (helds.take 3).all (·.contains 0))
        s!"sieve: no process holds a name twice, and of {helds.length} only the first three hold name 0")
      IO.println (line (part "process 12: " text == "process 12: []; holds [#11, #1]")
        s!"sieve: {part "process 12: " text}")
