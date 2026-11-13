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
  for name in ["ping", "race", "guess"] do
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
          part "refused: " text == "refused: [999, [2, 7, 8]] cannot happen")
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
