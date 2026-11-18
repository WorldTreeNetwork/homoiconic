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
      -- The entries here are written as a mark and an answer; the session
      -- seals each as it reads the log, so the fold is given the same seals.
      match vmRun 100000000 t (log.map fun e => Entry.seal entryName e.id e.answer) with
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

/-- A piece saved as the session saves a state, in a store of its own. -/
def keptPiece (state : P Ref) : String × Pieces :=
  match save pieceSize state with
  | some (root, pieces) => (hex root, pieces.foldl (fun m rb => m.insert rb.1 rb.2) {})
  | none => ("", {})

def list (ps : List (P Ref)) : P Ref := ps.foldr .cons .nil

-- Pieces that hash to their names and are not states are refused.
#eval do
  let result : P Ref := list [.nat 1, .nat 42]
  let function : P Ref := .closure (compile (.lit (.nat 42))) .nil
  let bad : List (String × P Ref) :=
    [ ("a third part", list [.nil, result, .nat 99]),
      ("a status with a third part", list [.nil, list [.nat 1, .nat 42, .nat 99]]),
      ("a list that does not end", .cons .nil (.cons result (.nat 5))),
      ("a result that holds a function", list [.nil, list [.nat 1, function]]),
      ("a waiting program that is not a function", list [.nil, list [.nat 0, .nat 3]]),
      ("an identifier list that is a number", list [.nat 4, result]),
      ("an unknown status", list [.nil, list [.nat 9]]) ]
  for (what, piece) in bad do
    let (root, m) := keptPiece piece
    let (text, _) := finish m 1000 (vmFrom root "[]".toUTF8 1000000)
    IO.println (line (text.startsWith "store error: the root is not a kept state")
      s!"refused: {what}")
  let (root, m) := keptPiece (list [.nil, result])
  let (text, _) := finish m 1000 (vmFrom root "[]".toUTF8 1000000)
  IO.println (line (text.startsWith "42\n") "a state of that shape is accepted")

-- The session's budget counts lazy steps, which are more than the plain
-- machine's: there is a budget the fold finishes in and the session does not.
#eval do
  let src ← IO.FS.readFile "../examples/ask.hom"
  let log : List Entry := [⟨.nat 1, .nat 20⟩, ⟨.nat 2, .nat 22⟩]
  let fold := match Surface.read src.toUTF8 with
    | .ok t => (vmRun 41 t log).isSome
    | .error _ => false
  let (text, _) := finish {} 1000 (vmStart src.toUTF8 (logText log) 41)
  IO.println (line (fold && text.startsWith "no result within 41 steps")
    "at 41 steps a turn the fold gives a state and the session gives none")

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
    -- An identifier is the hash of the whole entry: an entry with the mark of
    -- another and a different answer is a different entry, and is acted on.
    let (twice, _) := start [e1, ⟨e1.id, .nat 22⟩]
    IO.println (line (part "entries: " twice == "entries: 2 given, 2 acted on"
        && part "state: " twice == foldState src [e1, ⟨e1.id, .nat 22⟩]
        && part "state: " twice != state [e1, e2])
      s!"{name}: two answers under one mark are two entries")
    -- The order of first deliveries matters.
    IO.println (line (state [e2, e1] != state [e1, e2])
      s!"{name}: another order is another state")

-- An identifier that is a name is not the identifier that is its number
-- (`Data.decEq`): both are acted on, and each delivered again is not. This is
-- the proved fold on identifiers given directly, not sealed ones.
#eval do
  let src ← IO.FS.readFile "../examples/ask.hom"
  match Surface.read src.toUTF8 with
  | .error _ => IO.println (line false "names as identifiers: ask.hom does not read")
  | .ok t =>
    let seen (log : List Entry) : Option (List Data) := (vmRun budget t log).map fun (v : MVm) => v.seen
    let both := seen [⟨.name 7, .nat 20⟩, ⟨.nat 7, .nat 22⟩]
    let again := seen [⟨.name 7, .nat 20⟩, ⟨.name 7, .nat 1⟩, ⟨.nat 7, .nat 22⟩, ⟨.nat 7, .nat 1⟩, ⟨.name 7, .nat 1⟩]
    let one := seen [⟨.name 7, .nat 20⟩, ⟨.name 7, .nat 22⟩]
    IO.println (line (both == some [Data.nat 7, Data.name 7] && again == both && one == some [Data.name 7])
      "the identifiers #7 and 7 are two, and each delivered again is not acted on")
    -- An answer that is a name value is a name in the result.
    let result := match vmRun budget t [⟨.nat 1, .name 20⟩, ⟨.nat 2, .nat 22⟩] with
      | some v => (match v.status with
          | .finished (.value (.data d)) => Surface.renderData d
          | _ => "not a result")
      | none => "unfinished"
    IO.println (line (result == "[]") s!"add of an answer that is the name #20 and 22: {result}")

-- The name of an entry is the Blake3 hash of its bytes as one number: below
-- 2^256, different for the entries here, and the same whenever it is asked.
#eval do
  let name (d : Data) : Nat := match entryName d with | .nat n => n | _ => 0
  let a := name (.arr [.nat 1, .nat 20])
  let b := name (.arr [.nat 1, .nat 22])
  let c := name (.arr [.nat 2, .nat 20])
  let bytes := Blake3.hash (write (.arr [.nat 1, .nat 20]))
  IO.println (line (a / 2 ^ 256 == 0 && a != b && a != c && b != c && a == name (.arr [.nat 1, .nat 20])
      && a / 2 ^ 248 == (bytes.get! 0).toNat && a % 256 == (bytes.get! 31).toNat)
    "an entry's name is its hash as a number, first byte highest")
