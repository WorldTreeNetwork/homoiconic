import Surface.Run
import Wire.Piece
import Reflect.Store
import Reflect.Log
import Reflect.Node
import Surface.Chan
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

    A session can also be a node applying a log of ops (`Reflect.Node`):
    several processes, each event run as the jobs of its plan
    (`Reflect.plan`), and the node saved at the end as the piece
    `[seen, names, processes]`. A process is `[held, status]`, and a waiting
    status there also holds the payload: `[0, function, payload]`. The names
    made and the names held are kept as plain numbers; a name value in a
    payload, a result or a function is kept as a name.

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

/-- How a process of a node has finished. -/
inductive Final where
  | value (d : Data)
  | unbound (i : Nat)
  | wrong

/-- A node's processes: a function is held as a piece. -/
abbrev LConfig := Config (P Ref) Final

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
  /-- A kept node, being read. -/
  | openingNode (root : P Ref)
  /-- A node's machine run has ended where `st` says. -/
  | landed (st : Status (P Ref) Final)
  /-- A node between machine runs. -/
  | step
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

/-- An event a node is part way through: the runs still to do, where the runs
    done have ended, and the configuration once all have. -/
structure Doing where
  /-- `none` for the first run of all, which begins the program. -/
  op : Option Op
  jobs : List (Job (P Ref))
  got : List (Status (P Ref) Final) := []
  done : List (Status (P Ref) Final) → Option LConfig

/-- The part of a session that makes it a node applying a log. -/
structure NodePart where
  todo : List Op
  seen : List Data := []
  given : Nat
  acted : Nat := 0
  cfg : LConfig := ⟨[], []⟩
  doing : Option Doing := none

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
  /-- Set when the session is a node applying a log. -/
  node : Option NodePart := none

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

def plist (ps : List (P Ref)) : P Ref := ps.foldr .cons .nil

def statusPiece : Status (P Ref) Final → P Ref
  | .waiting k d => plist [.nat 0, k, d.toP]
  | .finished (.value d) => plist [.nat 1, d.toP]
  | .finished (.unbound i) => plist [.nat 2, .nat i]
  | .finished .wrong => plist [.nat 3]

def renderNodeProcs : Nat → List (Proc (P Ref) Final) → String
  | _, [] => ""
  | i, q :: qs =>
    s!"process {i}: " ++
      (match q.status with
       | .waiting _ p => "waiting on " ++ renderData p
       | .finished (.value d) => renderData d
       | .finished (.unbound k) => renderMOutcome (.unbound k)
       | .finished .wrong => renderMOutcome .wrong) ++
      "; holds " ++ renderData (.arr (q.held.map .name)) ++ "\n" ++ renderNodeProcs (i + 1) qs

/-- The log is applied, or an op of it cannot happen: save the node as it
    stands and say where each process is. -/
def Session.keepNode (s : Session) (part : NodePart) (refused : Option (Nat × Op)) : Session :=
  let procs := plist (part.cfg.procs.map fun q =>
    plist [Data.toP (.arr (q.held.map .nat)), statusPiece q.status])
  let state := plist [Data.toP (.arr part.seen), Data.toP (.arr (part.cfg.names.map .nat)), procs]
  match save pieceSize state with
  | none => s.finish "error: the node has no byte form"
  | some (root, pieces) =>
      let fresh := s.fresh pieces
      let stop := match refused with
        | some (k, o) => s!"refused: entry {k}, {renderData (eventData o.event)}, cannot happen\n"
        | none => ""
      { s with phase := .done, written := fresh,
               text := renderNodeProcs 0 part.cfg.procs ++
                 s!"entries: {part.given} given, {part.acted} acted on\n" ++ stop ++
                 s!"state: {hex root}\nstore: fetched {s.fetched}, wrote {fresh.size}" }

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
  | .name n => .ok (some (.name n))
  | .text t => .ok (some (.text t))
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

/-- The parts of a list piece, behind any references. `none` when the piece is
    not a list. -/
partial def parts (σ : Store Ref) (p : P Ref) : Except Ref (Option (List (P Ref))) := do
  match ← chase σ p with
  | (_, .nil) => pure (some [])
  | (_, .cons h t) =>
      match ← parts σ t with
      | some xs => pure (some (h :: xs))
      | none => pure none
  | _ => pure none

def natsOf : Data → Option (List Nat)
  | .arr ds => ds.mapM fun
      | .nat n => some n
      | _ => none
  | _ => none

def openStatus (σ : Store Ref) (p : P Ref) : Except Ref (Option (Status (P Ref) Final)) := do
  let some ps ← parts σ p | pure none
  match ps with
  | [tag, a, b] =>
      match ← chase σ tag, ← chase σ a with
      | (_, .nat 0), (held, .closure _ _) =>
          match ← full σ b with
          | some d => pure (some (.waiting held d))
          | none => pure none
      | _, _ => pure none
  | [tag, a] =>
      match ← chase σ tag with
      | (_, .nat 1) =>
          match ← full σ a with
          | some d => pure (some (.finished (.value d)))
          | none => pure none
      | (_, .nat 2) =>
          match ← chase σ a with
          | (_, .nat i) => pure (some (.finished (.unbound i)))
          | _ => pure none
      | _ => pure none
  | [tag] =>
      match ← chase σ tag with
      | (_, .nat 3) => pure (some (.finished .wrong))
      | _ => pure none
  | _ => pure none

def openProcs (σ : Store Ref) : List (P Ref) → Except Ref (Option (List (Proc (P Ref) Final)))
  | [] => pure (some [])
  | q :: qs => do
      let some [heldP, statusP] ← parts σ q | pure none
      let some heldData ← full σ heldP | pure none
      let some held := natsOf heldData | pure none
      let some status ← openStatus σ statusP | pure none
      let some rest ← openProcs σ qs | pure none
      pure (some (⟨status, held⟩ :: rest))

/-- Read a kept node: the identifiers acted on, and the processes. The piece
    must be exactly `[seen, names, processes]`, each process `[held, status]`,
    with names numbers, a payload and a result data, and a waiting program a
    function. As for a VM state, a function's environment is not walked. What
    the piece says a process is waiting on and holds is taken as it is. -/
def openNode (σ : Store Ref) (root : P Ref) : Except Ref (Option (List Data × LConfig)) := do
  let some [seenP, namesP, procsP] ← parts σ root | pure none
  let some (.arr seen) ← full σ seenP | pure none
  let some namesData ← full σ namesP | pure none
  let some names := natsOf namesData | pure none
  let some qs ← parts σ procsP | pure none
  let some procs ← openProcs σ qs | pure none
  pure (some (seen, ⟨procs, names⟩))

/-- Carry the turn on until it is over or needs a piece. For one turn, each
    phase is entered at most once in a call and the phases come in one order;
    a VM goes through them once for each entry it acts on. `fuel` above that
    number is never used up; if it were, the turn says so and is over.
    This follows `Reflect.driveRun` for one turn and `Reflect.vmRun` for a
    log, on the lazy machine. The budget counts the lazy machine's steps,
    which are more than the plain machine's (looking up a variable takes
    steps of its own), so a budget that is enough for `vmRun` may not be
    enough here. When both give a state, `LogCheck.lean` checks on examples
    that it is the same one.

    A node goes through the phases once for each machine run of each event.
    Which runs an event needs, whether it can happen, and the configuration
    after it are `Reflect.plan`'s, the function `plan_step` and `step_plan`
    are about. Running the jobs on the lazy machine and joining them is this
    function's, compared with `Reflect.nodeRun` in `NodeCheck.lean`. -/
def advance : Nat → Session → Session
  | 0, s => s.finish "error: the turn did not settle"
  | fuel + 1, s =>
      match s.phase with
      | .run st =>
          match steps s.store s.left st with
          | (.paused r st', left) => { s with phase := .run st', left, need := some r }
          | (.at (.halted (.value v)), _) => advance fuel { s with phase := .classify v }
          | (.at st', _) =>
              match s.node, st' with
              | some _, .halted (.unbound i) =>
                  advance fuel { s with phase := .landed (.finished (.unbound i)) }
              | some _, .halted .wrong =>
                  advance fuel { s with phase := .landed (.finished .wrong) }
              | _, _ => s.stopped st'
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
          | (.at st', _) =>
              match s.node, st' with
              | some _, .halted (.unbound i) =>
                  advance fuel { s with phase := .landed (.finished (.unbound i)) }
              | some _, .halted .wrong =>
                  advance fuel { s with phase := .landed (.finished .wrong) }
              | _, _ => s.stopped st'
      | .ask k p =>
          match full s.store p with
          | .error r => { s with need := some r }
          | .ok (some d) =>
              match s.node, s.vm with
              | some _, _ => advance fuel { s with phase := .landed (.waiting k d) }
              | none, none => s.wait d k
              | none, some part =>
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
          | .ok none =>
              match s.node with
              | some _ => advance fuel { s with phase := .landed (.finished .wrong) }
              | none => s.ended (renderMOutcome .wrong) (.cons (.nat 3) .nil)
      | .result p =>
          match full s.store p with
          | .error r => { s with need := some r }
          | .ok (some d) =>
              match s.node with
              | some _ => advance fuel { s with phase := .landed (.finished (.value d)) }
              | none => s.ended (renderData d) (.cons (.nat 1) (.cons d.toP .nil))
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
      | .openingNode root =>
          match openNode s.store root, s.node with
          | .error r, _ => { s with need := some r }
          | .ok (some (seen, cfg)), some part =>
              advance fuel { s with node := some { part with seen := seen, cfg := cfg },
                                    phase := .step }
          | _, _ => s.finish "store error: the root is not a kept node"
      | .landed st =>
          match s.node with
          | some part =>
              match part.doing with
              | some d =>
                  let part := { part with doing := some { d with got := d.got ++ [st] } }
                  advance fuel { s with node := some part, phase := .step }
              | none => s.finish "error: the turn did not settle"
          | none => s.finish "error: the turn did not settle"
      | .step =>
          match s.node with
          | none => s.finish "error: the turn did not settle"
          | some part =>
              match part.doing with
              | some d =>
                  match d.jobs with
                  | job :: jobs =>
                      let first : PState Ref := match job with
                        | .turn k a => .running (compile (resumeTerm a)) (.cons k .nil) [] []
                        | .start t => (load (compile t)).toP
                      let part := { part with doing := some { d with jobs := jobs } }
                      advance fuel { s with left := s.budget, node := some part,
                                            phase := .run first }
                  | [] =>
                      match d.done d.got with
                      | none => s.finish "error: the event did not settle"
                      | some cfg =>
                          let part := match d.op with
                            | some o => { part with cfg := cfg, doing := none,
                                                    seen := o.id :: part.seen,
                                                    acted := part.acted + 1 }
                            | none => { part with cfg := cfg, doing := none }
                          advance fuel { s with node := some part, phase := .step }
              | none =>
                  -- `Reflect.nodeRun`: an op whose identifier was acted on is
                  -- passed over; the next one happens, or cannot.
                  match part.todo.dropWhile (fun o => decide (o.id ∈ part.seen)) with
                  | [] => s.keepNode { part with todo := [] } none
                  | o :: rest =>
                      match plan part.cfg o.event with
                      | none => s.keepNode { part with todo := [] }
                          (some (part.given - (rest.length + 1), o))
                      | some (jobs, done) =>
                          let part := { part with todo := rest,
                                                  doing := some { op := some o, jobs, done } }
                          advance fuel { s with node := some part, phase := .step }
      | .done => s

/-- Enough for what is left of the session. -/
def Session.fuel (s : Session) : Nat :=
  8 + 4 * (match s.vm with
    | some part => part.todo.length
    | none => 0)
    + (match s.node with
    | some part => 40 + 20 * part.todo.length
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

/-- The name of an entry: the Blake3 hash of its bytes, read as one number,
    first byte highest. That two different entries do not share a name is
    assumed of the hash (D5), and needs `Wire.write` to give different data
    different bytes, which is tested and not proved. -/
def entryName (d : Data) : Data :=
  .nat ((Blake3.hash (write d)).foldl (fun n b => n * 256 + b.toNat) 0)

/-- The entries of a log given as data, each sealed under `entryName`, or the
    place of the first that is not a mark and an answer. -/
def dataEntries : Nat → List Data → Except Nat (List Entry)
  | _, [] => .ok []
  | k, .arr [mark, answer] :: ds =>
      (dataEntries (k + 1) ds).map (Entry.seal entryName mark answer :: ·)
  | k, _ :: _ => .error k

/-- Read a log: a program whose result is an array of `[mark, answer]`. -/
def readLog (src : ByteArray) (budget : Nat) : Except String (List Entry) :=
  match Surface.read src with
  | .error msg => .error ("log: " ++ renderSyntaxError msg)
  | .ok t =>
      match runUntil budget (load (compile t)) with
      | .halted (.value (.data (.arr ds))) =>
          match dataEntries 0 ds with
          | .error k => .error s!"log: entry {k} is not a mark and an answer"
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

/-- The ops of a log given as data, each sealed under `entryName`, or the
    place of the first that is not a mark and an event. -/
def dataOps : Nat → List Data → Except Nat (List Op)
  | _, [] => .ok []
  | k, .arr [mark, ev] :: ds =>
      match dataEvent ev with
      | some e => (dataOps (k + 1) ds).map (Op.seal entryName mark ev e :: ·)
      | none => .error k
  | k, _ :: _ => .error k

/-- Read a node's log: a program whose result is an array of
    `[mark, event]`. -/
def readOps (src : ByteArray) (budget : Nat) : Except String (List Op) :=
  match Surface.read src with
  | .error msg => .error ("log: " ++ renderSyntaxError msg)
  | .ok t =>
      match runUntil budget (load (compile t)) with
      | .halted (.value (.data (.arr ds))) =>
          match dataOps 0 ds with
          | .error k => .error s!"log: entry {k} is not a mark and an event"
          | .ok os => .ok os
      | _ => .error "log: not an array"

/-- A node from the start: the program is the first process, and the log is
    applied. -/
def nodeStart (program log : ByteArray) (budget : Nat) : Session :=
  match Surface.read program with
  | .error msg => failed (renderSyntaxError msg)
  | .ok t =>
      match readOps log budget with
      | .error msg => failed msg
      | .ok os =>
          let first : Doing := { op := none, jobs := [.start t], done := fun
            | [st] => some ⟨[⟨st, []⟩], []⟩
            | _ => none }
          let s : Session := { phase := .step, budget, left := budget,
                               node := some { todo := os, given := os.length,
                                              doing := some first } }
          advance s.fuel s

/-- A node from the one kept under `root`: the log is applied from there. -/
def nodeFrom (root : String) (log : ByteArray) (budget : Nat) : Session :=
  match unhex root with
  | none => failed "store error: a root is 64 hex digits"
  | some r =>
      match readOps log budget with
      | .error msg => failed msg
      | .ok os =>
          let s : Session := { phase := .openingNode (.ref r), budget, left := budget,
                               node := some { todo := os, given := os.length } }
          advance s.fuel s

end Surface.Keep
