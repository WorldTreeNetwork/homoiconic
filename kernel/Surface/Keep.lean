import Surface.Run
import Wire.Piece
import Reflect.Store
import Reflect.Log
import Std.Data.HashMap

/-! One turn of a program whose state is kept in a store between turns.

    A turn runs on the lazy machine (`Reflect.lstep`). When it needs a piece it
    does not hold, the session stops and names the piece; the caller supplies
    its bytes and the session carries on from where it stopped. When the turn
    ends in a request, the waiting program is cut, each new piece is named by
    the hash of its bytes, and the root is reported.

    A session can also be a VM handling a log (`Reflect.Log`): it carries on
    from one entry to the next, and what it saves at the end is the VM's state,
    the identifiers it has acted on and where its program stands. A state is
    the piece `[seen, status]`, where `status` is `[0, function]` for a waiting
    program, `[1, data]` for a result, `[2, i]` for the error of an unbound
    variable and `[3]` for the error `wrong`.

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
  /-- A kept VM state, being read. -/
  | opening (root : P Ref)
  | done

/-- The part of a session that makes it a VM handling a log. -/
structure VmPart where
  /-- Entries not handled yet. -/
  todo : List Entry
  /-- Identifiers acted on, newest first. -/
  seen : List Data := []
  /-- How many entries were given, and how many of them were acted on. -/
  given : Nat
  acted : Nat := 0

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
  /-- Set when the session is a VM handling a log. -/
  vm : Option VmPart := none

def Session.store (s : Session) : Store Ref := fun r => s.pieces[r]?

/-- A session that is over before it ran. -/
def failed (text : String) : Session :=
  { phase := .done, budget := 0, left := 0, text }

def Session.finish (s : Session) (text : String) : Session :=
  { s with phase := .done, text := s!"{text}\nstore: fetched {s.fetched}, wrote 0" }

/-- The turn ended in a request with payload `d`: save the waiting program.
    A piece already supplied is not written again, and a piece is written once. -/
def Session.fresh (s : Session) (pieces : Array (Ref × ByteArray)) : Array (Ref × ByteArray) :=
  (pieces.foldl (fun (acc : Std.HashMap Ref Unit × Array (Ref × ByteArray)) rb =>
    if s.pieces.contains rb.1 || acc.1.contains rb.1 then acc
    else (acc.1.insert rb.1 (), acc.2.push rb)) ({}, #[])).2

def Session.wait (s : Session) (d : Data) (k : P Ref) : Session :=
  match save pieceSize k with
  | none => s.finish "error: the waiting program has no byte form"
  | some (root, pieces) =>
      let fresh := s.fresh pieces
      { s with phase := .done, written := fresh,
               text := s!"asked: {renderData d}\nroot: {hex root}\nstore: fetched {s.fetched}, wrote {fresh.size}" }

/-- The log is handled: save the VM's state, whose program stands at `status`,
    and say where the program stands in `line`. -/
def Session.keepState (s : Session) (part : VmPart) (line : String) (status : P Ref) : Session :=
  let state : P Ref := .cons (Data.toP (.arr part.seen)) (.cons status .nil)
  match save pieceSize state with
  | none => s.finish "error: the state has no byte form"
  | some (root, pieces) =>
      let fresh := s.fresh pieces
      { s with phase := .done, written := fresh,
               text := s!"{line}\nentries: {part.given} given, {part.acted} acted on\nstate: {hex root}\nstore: fetched {s.fetched}, wrote {fresh.size}" }

/-- The program ended, with what `line` says. A VM is finished from here on:
    no entry left changes it. -/
def Session.ended (s : Session) (line : String) (status : P Ref) : Session :=
  match s.vm with
  | none => s.finish line
  | some part => s.keepState part line status

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
    there is a function in it. It ends when no piece reaches itself. That
    holds for pieces made by saving, where a reference is made after the piece
    it names. For other pieces it is assumed: a piece that reached itself
    would hold a hash of bytes that contain that hash. -/
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

/-- Follow references to the piece they name. Gives the last reference passed
    (or the piece, when it was not a reference) and the piece. `error r` when
    the store lacks `r`. It ends on the same condition as `full`. -/
partial def chase (σ : Store Ref) : P Ref → Except Ref (P Ref × P Ref)
  | .ref r =>
      match σ r with
      | none => .error r
      | some (.ref r') => chase σ (.ref r')
      | some p => .ok (.ref r, p)
  | p => .ok (p, p)

/-- What a run that stopped without a value says. -/
def Session.stopped (s : Session) : PState Ref → Session
  | .halted (.unbound i) =>
      s.ended (renderMOutcome (.unbound i)) (.cons (.nat 2) (.cons (.nat i) .nil))
  | .halted .wrong => s.ended (renderMOutcome .wrong) (.cons (.nat 3) .nil)
  | .fault => s.finish "error: machine fault"
  | _ => s.finish s!"no result within {s.budget} steps of a turn"

/-- Where a kept VM's program stands. -/
inductive Stands where
  | waiting (k : P Ref)
  | value (d : P Ref)
  | unbound (i : Nat)
  | wrong

/-- Is the piece, behind any references, the empty list? -/
def isNil (σ : Store Ref) (p : P Ref) : Except Ref Bool := do
  match ← chase σ p with
  | (_, .nil) => pure true
  | _ => pure false

/-- Read a kept VM state: the identifiers acted on, and where the program
    stands. `error r` when the store lacks `r`, `none` when the piece is not a
    state. The piece must be exactly `[seen, status]` with `seen` a list of
    data and `status` one of the four forms, a result being data and a waiting
    program a function. A function's environment is not walked: that would
    fetch what a turn may never look at. A function made by something other
    than saving may hold a part the machine cannot use, and a turn that
    reaches it ends in a machine fault and keeps nothing. -/
def openState (σ : Store Ref) (root : P Ref) : Except Ref (Option (List Data × Stands)) := do
  let (_, top) ← chase σ root
  let .cons seenP rest := top | pure none
  let some (.arr seen) ← full σ seenP | pure none
  let (_, .cons statusP last) ← chase σ rest | pure none
  if !(← isNil σ last) then return none
  let (_, .cons tagP body) ← chase σ statusP | pure none
  let (_, tag) ← chase σ tagP
  let (_, body) ← chase σ body
  match tag, body with
  | .nat 0, .cons k last =>
      if !(← isNil σ last) then return none
      match ← chase σ k with
      | (held, .closure _ _) => pure (some (seen, .waiting held))
      | _ => pure none
  | .nat 1, .cons d last =>
      if !(← isNil σ last) then return none
      let some _ ← full σ d | pure none
      pure (some (seen, .value d))
  | .nat 2, .cons i last =>
      if !(← isNil σ last) then return none
      match ← chase σ i with
      | (_, .nat n) => pure (some (seen, .unbound n))
      | _ => pure none
  | .nat 3, .nil => pure (some (seen, .wrong))
  | _, _ => pure none

/-- Carry the turn on until it is over or needs a piece. For one turn, each
    phase is entered at most once in a call and the phases come in one order;
    a VM goes through them once for each entry it acts on. `fuel` above that
    number is never used up; if it were, the turn says so and is over.
    This follows `Reflect.driveRun` for one turn and `Reflect.vmRun` for a
    log, on the lazy machine. The budget counts the lazy machine's steps,
    which are more than the plain machine's (looking up a variable takes
    steps of its own), so a budget that is enough for `vmRun` may not be
    enough here. When both give a state, `LogCheck.lean` checks on examples
    that it is the same one. -/
def advance : Nat → Session → Session
  | 0, s => s.finish "error: the turn did not settle"
  | fuel + 1, s =>
      match s.phase with
      | .run st =>
          match steps s.store s.left st with
          | (.paused r st', left) => { s with phase := .run st', left, need := some r }
          | (.at (.halted (.value v)), _) => advance fuel { s with phase := .classify v }
          | (.at st', _) => s.stopped st'
      | .classify v =>
          match chase s.store v with
          | .error r => { s with need := some r }
          | .ok (k, .closure _ _) =>
              -- `k` is the function as it is held: a reference when it was
              -- stored, so that saving it again writes nothing.
              let next := Phase.payload k
                (.running (compile payloadTerm) (.cons k .nil) [] [])
              advance fuel { s with left := s.budget, phase := next }
          | .ok (_, d) => advance fuel { s with phase := .result d }
      | .payload k st =>
          match steps s.store s.left st with
          | (.paused r st', left) => { s with phase := .payload k st', left, need := some r }
          | (.at (.halted (.value p)), _) => advance fuel { s with phase := .ask k p }
          | (.at st', _) => s.stopped st'
      | .ask k p =>
          match full s.store p with
          | .error r => { s with need := some r }
          | .ok (some d) =>
              match s.vm with
              | none => s.wait d k
              | some part =>
                  -- `Reflect.handleRun`: an entry whose identifier was acted on
                  -- is passed over, and the next one answers the request.
                  match part.todo.dropWhile (fun e => decide (e.id ∈ part.seen)) with
                  | [] =>
                      s.keepState part s!"waiting on {renderData d}"
                        (.cons (.nat 0) (.cons k .nil))
                  | e :: rest =>
                      let next := Phase.run
                        (.running (compile (resumeTerm e.answer)) (.cons k .nil) [] [])
                      let part := { part with todo := rest, seen := e.id :: part.seen,
                                              acted := part.acted + 1 }
                      advance fuel { s with left := s.budget, vm := some part, phase := next }
          | .ok none => s.ended (renderMOutcome .wrong) (.cons (.nat 3) .nil)
      | .result p =>
          match full s.store p with
          | .error r => { s with need := some r }
          | .ok (some d) => s.ended (renderData d) (.cons (.nat 1) (.cons d.toP .nil))
          | .ok none => s.finish "error: machine fault"
      | .opening root =>
          match openState s.store root with
          | .error r => { s with need := some r }
          | .ok none => s.finish "store error: the root is not a kept state"
          | .ok (some (seen, stands)) =>
              let s := { s with vm := s.vm.map (fun (part : VmPart) => { part with seen := seen }) }
              match stands with
              | .waiting k =>
                  let next := Phase.payload k
                    (.running (compile payloadTerm) (.cons k .nil) [] [])
                  advance fuel { s with left := s.budget, phase := next }
              | .value d => advance fuel { s with phase := .result d }
              | .unbound i => s.stopped (.halted (.unbound i))
              | .wrong => s.stopped (.halted .wrong)
      | .done => s

/-- Enough for what is left of the session. -/
def Session.fuel (s : Session) : Nat :=
  8 + 4 * (match s.vm with
    | some part => part.todo.length
    | none => 0)

/-- Begin a program from its source. -/
def start (src : ByteArray) (budget : Nat) : Session :=
  match Surface.read src with
  | .error msg => failed (renderSyntaxError msg)
  | .ok t =>
      let s : Session := { phase := .run (load (compile t)).toP, budget, left := budget }
      advance s.fuel s

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
              let s : Session := { budget, left := budget, phase := first }
              advance s.fuel s
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
            let s := { s with pieces := s.pieces.insert r p, need := none,
                              fetched := s.fetched + 1 }
            advance s.fuel s

/-- The entries of a log given as data, or the place of the first that is not
    an identifier and an answer. -/
def dataEntries : Nat → List Data → Except Nat (List Entry)
  | _, [] => .ok []
  | k, .arr [id, answer] :: ds => (dataEntries (k + 1) ds).map (⟨id, answer⟩ :: ·)
  | k, _ :: _ => .error k

/-- Read a log: a program whose result is an array of `[identifier, answer]`. -/
def readLog (src : ByteArray) (budget : Nat) : Except String (List Entry) :=
  match Surface.read src with
  | .error msg => .error ("log: " ++ renderSyntaxError msg)
  | .ok t =>
      match runUntil budget (load (compile t)) with
      | .halted (.value (.data (.arr ds))) =>
          match dataEntries 0 ds with
          | .error k => .error s!"log: entry {k} is not an identifier and an answer"
          | .ok es => .ok es
      | _ => .error "log: not an array"

/-- A VM from the start: run the program and handle the log. -/
def vmStart (program log : ByteArray) (budget : Nat) : Session :=
  match Surface.read program with
  | .error msg => failed (renderSyntaxError msg)
  | .ok t =>
      match readLog log budget with
      | .error msg => failed msg
      | .ok es =>
          let s : Session := { phase := .run (load (compile t)).toP, budget, left := budget,
                               vm := some { todo := es, given := es.length } }
          advance s.fuel s

/-- A VM from the state kept under `root`: handle the log from there. -/
def vmFrom (root : String) (log : ByteArray) (budget : Nat) : Session :=
  match unhex root with
  | none => failed "store error: a root is 64 hex digits"
  | some r =>
      match readLog log budget with
      | .error msg => failed msg
      | .ok es =>
          let s : Session := { phase := .opening (.ref r), budget, left := budget,
                               vm := some { todo := es, given := es.length } }
          advance s.fuel s

end Surface.Keep
