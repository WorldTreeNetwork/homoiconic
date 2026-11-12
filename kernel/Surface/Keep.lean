import Surface.Run
import Wire.Piece
import Reflect.Store
import Std.Data.HashMap

/-! One turn of a program whose state is kept in a store between turns.

    A turn runs on the lazy machine (`Reflect.lstep`). When it needs a piece it
    does not hold, the session stops and names the piece; the caller supplies
    its bytes and the session carries on from where it stopped. When the turn
    ends in a request, the waiting program is cut, each new piece is named by
    the hash of its bytes, and the root is reported.

    Each machine run here is covered by `Reflect.lazy_turn_complete` and
    `Reflect.lazy_turn_sound`. The session that joins the runs, the hashing
    and the byte forms are tested, not proved. -/

namespace Surface.Keep
open Reflect Wire

/-- A stored piece is cut loose from its parent above this many bytes. -/
def pieceSize : Nat := 256

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n]!

def hex (b : ByteArray) : String :=
  String.ofList (b.toList.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

def unhexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else none

/-- A reference from its name: 64 lower-case hex digits. -/
def unhex (s : String) : Option Ref :=
  let rec go : List Char → ByteArray → Option ByteArray
    | [], out => some out
    | a :: b :: rest, out =>
        match unhexDigit a, unhexDigit b with
        | some x, some y => go rest (out.push (x * 16 + y).toUInt8)
        | _, _ => none
    | _, _ => none
  if s.length == 64 then go s.toList ByteArray.empty else none

/-- Where a turn is. -/
inductive Phase where
  /-- The turn's own run. -/
  | run (s : PState Ref)
  /-- The run gave a value; is it a function? -/
  | classify (v : P Ref)
  /-- It is a function `k`: the run that takes its payload. -/
  | payload (k : P Ref) (s : PState Ref)
  /-- The payload of `k`, being fetched whole. -/
  | ask (k : P Ref) (p : P Ref)
  /-- A data result, being fetched whole. -/
  | result (p : P Ref)
  | done

structure Session where
  /-- Pieces supplied so far, by reference. -/
  pieces : Std.HashMap Ref (P Ref) := {}
  phase : Phase
  /-- Steps each machine run may take, and steps left in the current one. -/
  budget : Nat
  left : Nat
  /-- The piece the turn cannot go on without. -/
  need : Option Ref := none
  fetched : Nat := 0
  /-- Pieces to be stored, by name. -/
  written : Array (Ref × ByteArray) := #[]
  text : String := ""

def Session.store (s : Session) : Store Ref := fun r => s.pieces[r]?

/-- A session that is over before it ran. -/
def failed (text : String) : Session :=
  { phase := .done, budget := 0, left := 0, text }

def Session.finish (s : Session) (text : String) : Session :=
  { s with phase := .done, text := s!"{text}\nstore: fetched {s.fetched}, wrote 0" }

/-- The turn ended in a request with payload `d`: save the waiting program.
    A piece already supplied is not written again, and a piece is written once. -/
def Session.wait (s : Session) (d : Data) (k : P Ref) : Session :=
  match save pieceSize k with
  | none => s.finish "error: the waiting program has no byte form"
  | some (root, pieces) =>
      let fresh := pieces.foldl (fun (acc : Std.HashMap Ref Unit × Array (Ref × ByteArray)) rb =>
        if s.pieces.contains rb.1 || acc.1.contains rb.1 then acc
        else (acc.1.insert rb.1 (), acc.2.push rb)) ({}, #[])
      { s with phase := .done, written := fresh.2,
               text := s!"asked: {renderData d}\nroot: {hex root}\nstore: fetched {s.fetched}, wrote {fresh.2.size}" }

/-- Lazy steps until the machine stops, pauses, or the budget ends, with the
    steps left. -/
def steps (σ : Store Ref) : Nat → PState Ref → LRun Ref × Nat
  | 0, s => (.at s, 0)
  | n + 1, s =>
      match s with
      | .halted _ => (.at s, n + 1)
      | .fault => (.at s, n + 1)
      | _ =>
          match lstep σ s with
          | .next s' => steps σ n s'
          | .needs r => (.paused r s, n + 1)

/-- A piece as whole data: `error r` when the store lacks `r`, `none` when
    there is a function in it. It ends because a reference is the hash of the
    piece it names, so no piece can reach itself. -/
partial def full (σ : Store Ref) : P Ref → Except Ref (Option Data)
  | .nat n => .ok (some (.nat n))
  | .nil => .ok (some (.arr []))
  | .cons h t => do
      match ← full σ h, ← full σ t with
      | some x, some (.arr xs) => pure (some (.arr (x :: xs)))
      | _, _ => pure none
  | .closure _ _ => .ok none
  | .ref r =>
      match σ r with
      | some p => full σ p
      | none => .error r

/-- What a run that stopped without a value says. -/
def Session.stopped (s : Session) : PState Ref → Session
  | .halted (.unbound i) => s.finish (renderMOutcome (.unbound i))
  | .halted .wrong => s.finish (renderMOutcome .wrong)
  | .fault => s.finish "error: machine fault"
  | _ => s.finish s!"no result within {s.budget} steps of a turn"

/-- Carry the turn on until it is over or needs a piece. Each phase is entered
    at most once, apart from following a reference, so a small `fuel` is never
    used up. This is `Reflect.driveRun` for one turn, on the lazy machine. -/
def advance : Nat → Session → Session
  | 0, s => s
  | fuel + 1, s =>
      match s.phase with
      | .run st =>
          match steps s.store s.left st with
          | (.paused r st', left) => { s with phase := .run st', left, need := some r }
          | (.at (.halted (.value v)), _) => advance fuel { s with phase := .classify v }
          | (.at st', _) => s.stopped st'
      | .classify (.ref r) =>
          match s.store r with
          | some (.closure _ _) =>
              -- The function stays a reference, so saving it writes nothing.
              let next := Phase.payload (.ref r)
                (.running (compile payloadTerm) (.cons (.ref r) .nil) [] [])
              advance fuel { s with left := s.budget, phase := next }
          | some p => advance fuel { s with phase := .classify p }
          | none => { s with need := some r }
      | .classify (.closure c e) =>
          let next := Phase.payload (.closure c e)
            (.running (compile payloadTerm) (.cons (.closure c e) .nil) [] [])
          advance fuel { s with left := s.budget, phase := next }
      | .classify d => advance fuel { s with phase := .result d }
      | .payload k st =>
          match steps s.store s.left st with
          | (.paused r st', left) => { s with phase := .payload k st', left, need := some r }
          | (.at (.halted (.value p)), _) => advance fuel { s with phase := .ask k p }
          | (.at st', _) => s.stopped st'
      | .ask k p =>
          match full s.store p with
          | .error r => { s with need := some r }
          | .ok (some d) => s.wait d k
          | .ok none => s.finish (renderMOutcome .wrong)
      | .result p =>
          match full s.store p with
          | .error r => { s with need := some r }
          | .ok (some d) => s.finish (renderData d)
          | .ok none => s.finish "error: machine fault"
      | .done => s

def fuel : Nat := 64

/-- Begin a program from its source. -/
def start (src : ByteArray) (budget : Nat) : Session :=
  match Surface.read src with
  | .error msg => failed (renderSyntaxError msg)
  | .ok t => advance fuel { phase := .run (load (compile t)).toP, budget, left := budget }

/-- Answer the waiting program stored under `root`. The answer is a program
    whose result is the data to give. -/
def answer (root : String) (src : ByteArray) (budget : Nat) : Session :=
  match unhex root with
  | none => failed "store error: a root is 64 hex digits"
  | some r =>
      match Surface.read src with
      | .error msg => failed ("answer: " ++ renderSyntaxError msg)
      | .ok t =>
          match runUntil budget (load (compile t)) with
          | .halted (.value (.data d)) =>
              let first := Phase.run
                (.running (compile (resumeTerm d)) (.cons (.ref r) .nil) [] [])
              advance fuel { budget, left := budget, phase := first }
          | _ => failed "answer: not data"

/-- Supply the piece the session needs. The bytes must hash to its name. -/
def give (s : Session) (bytes : ByteArray) : Session :=
  match s.need with
  | none => s
  | some r =>
      if hex (Blake3.hash bytes) != hex r then
        failed s!"store error: piece {hex r} does not match its name"
      else
        match readPiece bytes with
        | .error msg => failed s!"store error: piece {hex r}: {msg}"
        | .ok p =>
            advance fuel { s with pieces := s.pieces.insert r p, need := none,
                                  fetched := s.fetched + 1 }

end Surface.Keep
