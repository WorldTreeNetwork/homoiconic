import Reflect.Arith
import Reflect
import Wire
import Surface
open Reflect Wire Surface.Keep

/-! Tests the VM session (`Surface.Keep.vmStart`, `vmFrom`) against the proved
    fold (`Reflect.vmRun`): the state the session saves has the root that the
    fold's state has when it is saved the same way, whether the session began
    at the program or at a kept state. Each line that starts with FAIL fails
    the check. -/

def line (ok : Bool) (what : String) : String := s!"{if ok then "ok  " else "FAIL"} {what}"

abbrev Pieces := Std.HashMap Ref ByteArray

/-- The host's part for one session: supply pieces, then store what was written. -/
def finish (m : Pieces) : Nat → Session → String × Pieces
  | 0, _ => ("did not finish", m)
  | fuel + 1, s =>
      match s.need with
      | some r =>
          match m[r]? with
          | some b => finish m fuel (give s b)
          | none => ("lacks a piece", m)
      | none => (s.text, s.written.foldl (fun m rb => m.insert rb.1 rb.2) m)

def part (prefix_ : String) (text : String) : String :=
  ((text.splitOn "\n").find? (·.startsWith prefix_)).getD ""

def logText (es : List Entry) : ByteArray :=
  (Surface.renderData (.arr (es.map fun e => .arr [e.id, e.answer]))).toUTF8

/-- The state of the proved fold, saved as the session saves a state. -/
def foldState (src : String) (log : List Entry) : String :=
  match Surface.read src.toUTF8 with
  | .error _ => "syntax error"
  | .ok t =>
      match vmRun 100000000 t log with
      | none => "unfinished"
      | some v =>
          let status : Option (P Ref) :=
            match v.status with
            | .waiting c _ => some (.cons (.nat 0) (.cons c.toP .nil))
            | .finished (.value (.data d)) => some (.cons (.nat 1) (.cons d.toP .nil))
            | .finished (.unbound i) => some (.cons (.nat 2) (.cons (.nat i) .nil))
            | .finished .wrong => some (.cons (.nat 3) .nil)
            | _ => none
          match status.bind fun st =>
              save pieceSize (.cons (Data.toP (.arr v.seen)) (.cons st .nil)) with
          | some (root, _) => "state: " ++ hex root
          | none => "no state"

def e1 : Entry := ⟨.arr [.nat 7], .nat 20⟩
def e2 : Entry := ⟨.nat 8, .nat 22⟩
def e3 : Entry := ⟨.nat 9, .nat 1⟩

def budget : Nat := 100000000

#eval do
  for name in ["keep", "ask"] do
    let src ← IO.FS.readFile s!"../examples/{name}.hom"
    let start (log : List Entry) : String × Pieces :=
      finish {} 100000 (vmStart src.toUTF8 (logText log) budget)
    let state (log : List Entry) : String := part "state: " (start log).1
    -- From the start, the session and the fold agree at every length of log.
    for log in [[], [e1], [e1, e2], [e1, e2, e3]] do
      IO.println (line (state log == foldState src log && (state log).length == 71)
        s!"{name}: the session and the fold agree after {log.length} entries")
    -- A state kept after one entry, given the whole log, gets where the whole
    -- log gets from the start, and acts only on the entry it had not seen.
    let (text, m) := start [e1]
    let root := ((part "state: " text).drop 7).toString
    let (later, _) := finish m 100000 (vmFrom root (logText [e1, e2]) budget)
    IO.println (line (part "state: " later == state [e1, e2])
      s!"{name}: a kept state restarted on the whole log reaches the same state")
    IO.println (line (part "entries: " later == "entries: 2 given, 1 acted on")
      s!"{name}: restarted, {part "entries: " later}")
    -- Deliveries that repeat change nothing.
    IO.println (line (state [e1, e1, e2, e1, e2] == state [e1, e2])
      s!"{name}: repeats leave the state as it is")
    -- A finished VM, kept and given more, is the same state.
    let (done, m2) := start [e1, e2]
    let (again, _) := finish m2 100000 (vmFrom ((part "state: " done).drop 7).toString (logText [e3]) budget)
    IO.println (line (part "state: " again == part "state: " done && (done.splitOn "\n").head? == (again.splitOn "\n").head?)
      s!"{name}: a finished VM stays as it is: {(again.splitOn "\n").headD ""}")
    -- The order of first deliveries matters.
    IO.println (line (state [e2, e1] != state [e1, e2])
      s!"{name}: another order is another state")
