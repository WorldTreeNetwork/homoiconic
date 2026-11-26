import Surface.Run
import Wire.Piece
import Reflect.Store
import Reflect.StoreSpace
import Std.Data.HashSet
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
    and the byte forms are tested, not proved. That a state is saved under one
    root however much of it is held as references is proved, for references
    that saving made (`Surface/KeepProof.lean`, `Wire/PieceProof.lean`). That
    a session holds and saves only such references is proved too: for one
    turn of a program (`advance_turn`), and for every session, a VM and a
    node among them (`advance_kept`, `Surface/KeepLogProof.lean`). That what a
    VM or a node saves stands for the state the log theorems speak of is not
    proved.

    A turn that answers a waiting program does not hold the root as a
    reference when the piece under it is small (`Wire.opened`): saving stores
    the top piece whatever its size, and a reference to a small piece is one
    saving never makes inside a value. -/

namespace Surface.Keep
open Reflect Wire

/-- Identifiers are looked up in a hash set beside the list they are kept in
    (`homoiconic-q59.78`): hashed by their bytes, compared by `Data.same`. -/
instance : Hashable Data := ⟨fun d => hash (write d)⟩

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
  /-- The waiting program under the root `r`, about to be answered with `d`. -/
  | resuming (r : Ref) (d : Data)
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
  /-- The same identifiers, to look one up at once. -/
  seenSet : Std.HashSet Data := {}
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
  seenSet : Std.HashSet Data := {}
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
  /-- The cells each machine run may make (`Reflect.lrunSpace`), and what is
      left of them in the current one. -/
  cells : Nat := defaultSpace
  credit : Nat := defaultSpace
  /-- How many cells the session holds, from the runtime, given its phase and
      the state of the run: asked when the credit is spent. `none`: the
      ledger alone. A host gives it (`Surface.Host`). -/
  count : Option (Phase → PState Ref → Nat) := none
  /-- The bytes of the pieces given: no fewer than their cells. The pieces'
      map is not walked by the runtime's count. -/
  held : Nat := 0

/-- The space a machine run of the session has: its cells, and the count
    with the pieces given on top, or the ledger alone. -/
def Session.space (s : Session) : LSpace Ref :=
  ⟨s.cells, fun ps => match s.count with
    | some f => f s.phase ps + s.held
    | none => s.cells + 1⟩

def Session.store (s : Session) : Store Ref := fun r => s.pieces[r]?

/-- More than the references a chain can pass through the pieces supplied
    without meeting one twice. -/
def Session.reach (s : Session) : Nat := s.pieces.size + 1

/-- A session that is over before it ran. -/
def failed (text : String) : Session :=
  { phase := .done, budget := 0, left := 0, text }

def Session.finish (s : Session) (text : String) : Session :=
  { s with phase := .done, text := s!"{text}\nstore: fetched {s.fetched}, wrote 0" }

/-- A turn that would make more cells than it may, or whose result would be
    more than four bytes written a cell: the space line, as a run has it. -/
def Session.outOfSpace (s : Session) : Session :=
  s.finish s!"no result within {s.cells} cells of a turn"

/-- The name `full` gives for a value too large to read: no piece has it, a
    piece's name being 32 bytes. -/
def tooLarge : Ref := ByteArray.empty

/-- The walk cannot go on without the piece `r`, or (`tooLarge`) at all. -/
def Session.stuck (s : Session) (r : Ref) : Session :=
  if r.size == 0 then s.outOfSpace else { s with need := some r }

/-- Units a piece is counted at, each part where it is held: a number or a
    name five and its written digits, a text seven and four a character, an
    empty list two, a pair five, a reference one, a function one. At least
    what `Data.written` counts for data. -/
def unit : P Ref → Nat
  | .nat n => 5 + natWritten n
  | .name n => 5 + natWritten n
  | .text t => 7 + 4 * t.length
  | .nil => 2
  | .cons _ _ => 5
  | .ref _ => 1
  | .closure _ _ => 1

theorem unit_pos (p : P Ref) : 1 ≤ unit p := by cases p <;> simp only [unit] <;> omega

/-- Whether the pieces of `work`, a function's environment included and a
    reference not followed, are counted at no more than `left`. -/
def unitsGo : (left : Nat) → List (P Ref) → Bool
  | _, [] => true
  | left, p :: ps =>
      if left < unit p then false
      else match p with
        | .cons h t => unitsGo (left - unit p) (h :: t :: ps)
        | .closure _ e => unitsGo (left - unit p) (e :: ps)
        | _ => unitsGo (left - unit p) ps
termination_by left => left
decreasing_by all_goals (have := unit_pos p; omega)

/-- What a saved state may be counted at, and what reading one may cross:
    reading also passes the references saving made, at most one for every
    `pieceSize` bytes stored. -/
def Session.keepLimit (s : Session) : Nat := 4 * s.cells
def Session.readLimit (s : Session) : Nat := 5 * s.cells

/-- A state to be saved that is counted at more than `keepLimit`: saving
    walks it as a tree. -/
def Session.tooLargeToKeep (s : Session) (p : P Ref) : Bool := !unitsGo s.keepLimit [p]

/-- The turn ended in a request with payload `d`: save the waiting program.
    A piece already supplied is not written again, and a piece is written once. -/
def Session.fresh (s : Session) (pieces : Array (Ref × ByteArray)) : Array (Ref × ByteArray) :=
  (pieces.foldl (fun (acc : Std.HashMap Ref Unit × Array (Ref × ByteArray)) rb =>
    if s.pieces.contains rb.1 || acc.1.contains rb.1 then acc
    else (acc.1.insert rb.1 (), acc.2.push rb)) ({}, #[])).2

def Session.wait (s : Session) (d : Data) (k : P Ref) : Session :=
  if s.tooLargeToKeep k then
    s.finish s!"the waiting program is too large to keep within {s.cells} cells"
  else
  match save pieceSize k with
  | none => s.finish "error: the waiting program has no byte form"
  | some (root, pieces) =>
      let fresh := s.fresh pieces
      { s with phase := .done, written := fresh,
               text := s!"asked: {renderData d}\nroot: {hex root}\nstore: fetched {s.fetched}, wrote {fresh.size}" }

/-- A VM's state as one piece, `[seen, status]`: the identifiers it has acted
    on and where its program stands. -/
def vmState (seen : List Data) (status : P Ref) : P Ref :=
  .cons (Data.toP (.arr seen)) (.cons status .nil)

/-- The log is handled: save the VM's state, whose program stands at `status`,
    and say where the program stands in `line`. -/
def Session.keepState (s : Session) (part : VmPart) (line : String) (status : P Ref) : Session :=
  if s.tooLargeToKeep (vmState part.seen status) then
    s.finish s!"{line}\nthe state is too large to keep within {s.cells} cells"
  else
  match save pieceSize (vmState part.seen status) with
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

/-- One process's line of `renderNodeProcs`. -/
def renderNodeProc (i : Nat) (q : Proc (P Ref) Final) : String :=
  s!"process {i}: " ++
    (match q.status with
     | .waiting _ p => "waiting on " ++ renderData p
     | .finished (.value d) => renderData d
     | .finished (.unbound k) => renderMOutcome (.unbound k)
     | .finished .wrong => renderMOutcome .wrong) ++
    "; holds " ++ renderData (.arr (q.held.map .name)) ++ "\n"

/-- `renderNodeProcs` after `acc`, as a loop (`homoiconic-q59.78`). -/
def renderNodeProcsGo : Nat → String → List (Proc (P Ref) Final) → String
  | _, acc, [] => acc
  | i, acc, q :: qs => renderNodeProcsGo (i + 1) (acc ++ renderNodeProc i q) qs

theorem renderNodeProcsGo_eq : ∀ (qs : List (Proc (P Ref) Final)) (i : Nat) (acc : String),
    renderNodeProcsGo i acc qs = acc ++ renderNodeProcs i qs
  | [], i, acc => by simp [renderNodeProcsGo, renderNodeProcs]
  | q :: qs, i, acc => by
    rw [renderNodeProcsGo, renderNodeProcsGo_eq qs, renderNodeProcs, String.append_assoc]; rfl

def renderNodeProcsWalk (i : Nat) (qs : List (Proc (P Ref) Final)) : String :=
  renderNodeProcsGo i "" qs

@[csimp] theorem renderNodeProcs_eq_walk : @renderNodeProcs = @renderNodeProcsWalk := by
  funext i qs; simp [renderNodeProcsWalk, renderNodeProcsGo_eq]

/-- A node as one piece, `[seen, names, processes]`, each process
    `[held, status]`. -/
def nodePiece (seen : List Data) (cfg : LConfig) : P Ref :=
  let procs := plist (cfg.procs.map fun q =>
    plist [Data.toP (.arr (q.held.map .nat)), statusPiece q.status])
  plist [Data.toP (.arr seen), Data.toP (.arr (cfg.names.map .nat)), procs]

/-- The log is applied, or an op of it cannot happen: save the node as it
    stands and say where each process is. -/
def Session.keepNode (s : Session) (part : NodePart) (refused : Option (Nat × Op)) : Session :=
  if s.tooLargeToKeep (nodePiece part.seen part.cfg) then
    s.finish s!"the state is too large to keep within {s.cells} cells"
  else
  match save pieceSize (nodePiece part.seen part.cfg) with
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

/-- Lazy steps until the machine stops, pauses, the budget ends or the space
    does, with the budget and the credit left: `Reflect.lrunSpace` with the
    session's store and space. Each step is charged `lstepCost`, at least one,
    found within the budget left, before it is taken, as `Reflect.runPriced`
    charges the plain machine; a step the budget left cannot pay for is not
    taken, and the run ends at the state before it. -/
def steps (s : Session) (st : PState Ref) : LEnded Ref × Nat × Nat :=
  lrunSpace s.store s.space s.left s.credit st

/-- What is still to do in `fullGo`. -/
inductive FAct where
  | piece : P Ref → FAct
  | cons : FAct

/-- `full`'s walk: `left` is what it may still count (`unit`, each reference
    crossed one), and the data made so far waits on the stack. -/
def fullGo (σ : Store Ref) : (left : Nat) → List FAct → List Data → Except Ref (Option Data)
  | _, [], d :: _ => .ok (some d)
  | _, [], [] => .ok none
  | left, .piece p :: as, st =>
      if left < unit p then .error tooLarge
      else match p with
        | .nat n => fullGo σ (left - unit p) as (.nat n :: st)
        | .name n => fullGo σ (left - unit p) as (.name n :: st)
        | .text t => fullGo σ (left - unit p) as (.text t :: st)
        | .nil => fullGo σ (left - unit p) as (.arr [] :: st)
        | .cons h t => fullGo σ (left - unit p) (.piece h :: .piece t :: .cons :: as) st
        | .closure _ _ => .ok none
        | .ref r =>
            match σ r with
            | some q => fullGo σ (left - unit p) (.piece q :: as) st
            | none => .error r
  | left, .cons :: as, .arr xs :: x :: st => fullGo σ left as (.arr (x :: xs) :: st)
  | _, .cons :: _, _ => .ok none
termination_by left as => (left, as.length)
decreasing_by
  all_goals simp_wf
  all_goals (first
    | (apply Prod.Lex.left; have := unit_pos p; omega)
    | (apply Prod.Lex.right; omega))

/-- A piece as whole data: `error r` when the store lacks `r`, `none` when
    there is a function in it, and `error tooLarge` when it is counted at more
    than `limit` (`unit`, each reference crossed one), which bounds the time
    and the data. It looks at the head of a pair before the rest, and stops
    at the first function. What it gives is data, so no reference comes out of
    it. A walk over a list of work, not a call for each level
    (`homoiconic-q59.78`): it was `partial` and recursive. -/
def full (σ : Store Ref) (limit : Nat) (p : P Ref) : Except Ref (Option Data) :=
  fullGo σ limit [.piece p] []

/-- Follow references to the piece they name, through at most `n` of them.
    Gives the last reference passed (or the piece, when it was not a
    reference) and the piece. `error r` when the store lacks `r`. A chain that
    is longer than `n` is given back as the reference it has reached. With `n`
    above the number of pieces the store holds (`Session.reach`) that is a
    chain that meets a reference twice, which `full` does not end on. -/
def chase (σ : Store Ref) : Nat → P Ref → Except Ref (P Ref × P Ref)
  | n + 1, .ref r =>
      match σ r with
      | none => .error r
      | some (.ref r') => chase σ n (.ref r')
      | some p => .ok (.ref r, p)
  | _, p => .ok (p, p)

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
def isNil (σ : Store Ref) (n : Nat) (p : P Ref) : Except Ref Bool := do
  match ← chase σ n p with
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
def openState (σ : Store Ref) (n lim : Nat) (root : P Ref) : Except Ref (Option (List Data × Stands)) := do
  let (_, top) ← chase σ n root
  let .cons seenP rest := top | pure none
  let some (.arr seen) ← full σ lim seenP | pure none
  let (_, .cons statusP last) ← chase σ n rest | pure none
  if !(← isNil σ n last) then return none
  let (_, .cons tagP body) ← chase σ n statusP | pure none
  let (_, tag) ← chase σ n tagP
  let (_, body) ← chase σ n body
  match tag, body with
  | .nat 0, .cons k last =>
      if !(← isNil σ n last) then return none
      match ← chase σ n k with
      | (held, .closure _ _) => pure (some (seen, .waiting held))
      | _ => pure none
  | .nat 1, .cons d last =>
      if !(← isNil σ n last) then return none
      let some _ ← full σ lim d | pure none
      pure (some (seen, .value d))
  | .nat 2, .cons i last =>
      if !(← isNil σ n last) then return none
      match ← chase σ n i with
      | (_, .nat n) => pure (some (seen, .unbound n))
      | _ => pure none
  | .nat 3, .nil => pure (some (seen, .wrong))
  | _, _ => pure none

/-- The parts of a list piece, behind any references. `none` when the piece is
    not a list. The whole list may pass through at most `n` references; a
    list that passes through more is given as `none`. With `n` above the
    number of pieces the store holds (`Session.reach`) such a list meets a
    reference twice, so it has no end. -/
def parts (σ : Store Ref) : Nat → P Ref → Except Ref (Option (List (P Ref)))
  | _, .nil => .ok (some [])
  | n, .cons h t =>
      match parts σ n t with
      | .ok (some xs) => .ok (some (h :: xs))
      | .ok none => .ok none
      | .error r => .error r
  | n + 1, .ref r =>
      match σ r with
      | some p => parts σ n p
      | none => .error r
  | _, _ => .ok none
termination_by n p => (n, sizeOf p)

/-- `parts` with the parts found so far in `acc`, newest first: a loop, not a
    call for each item (`homoiconic-q59.78`). -/
def partsGo (σ : Store Ref) (acc : List (P Ref)) : Nat → P Ref → Except Ref (Option (List (P Ref)))
  | _, .nil => .ok (some acc.reverse)
  | n, .cons h t => partsGo σ (h :: acc) n t
  | n + 1, .ref r =>
      match σ r with
      | some p => partsGo σ acc n p
      | none => .error r
  | _, _ => .ok none
termination_by n p => (n, sizeOf p)

theorem partsGo_eq (σ : Store Ref) : ∀ (n : Nat) (p : P Ref) (acc : List (P Ref)),
    partsGo σ acc n p = (parts σ n p).map (Option.map (acc.reverse ++ ·))
  | _, .nil, acc => by rw [partsGo, parts]; simp [Except.map]
  | n, .cons h t, acc => by
    rw [partsGo, parts, partsGo_eq σ n t (h :: acc)]
    cases parts σ n t with
    | error r => rfl
    | ok o => cases o <;> simp [Except.map]
  | n + 1, .ref r, acc => by
    rw [partsGo, parts]
    cases hr : σ r with
    | some p => simp only []; exact partsGo_eq σ n p acc
    | none => rfl
  | 0, .ref r, acc => by rw [partsGo, parts] <;> first | rfl | (intros; simp_all)
  | _, .nat _, acc => by rw [partsGo, parts] <;> first | rfl | (intros; simp_all)
  | _, .name _, acc => by rw [partsGo, parts] <;> first | rfl | (intros; simp_all)
  | _, .text _, acc => by rw [partsGo, parts] <;> first | rfl | (intros; simp_all)
  | _, .closure _ _, acc => by rw [partsGo, parts] <;> first | rfl | (intros; simp_all)
termination_by n p => (n, sizeOf p)

def partsWalk (σ : Store Ref) (n : Nat) (p : P Ref) : Except Ref (Option (List (P Ref))) :=
  partsGo σ [] n p

@[csimp] theorem parts_eq_walk : @parts = @partsWalk := by
  funext σ n p
  rw [partsWalk, partsGo_eq]
  cases parts σ n p with
  | error r => rfl
  | ok o => cases o <;> simp [Except.map]

def natsOf : Data → Option (List Nat)
  | .arr ds => ds.mapM fun
      | .nat n => some n
      | _ => none
  | _ => none

def openStatus (σ : Store Ref) (n lim : Nat) (p : P Ref) : Except Ref (Option (Status (P Ref) Final)) := do
  let some ps ← parts σ n p | pure none
  match ps with
  | [tag, a, b] =>
      match ← chase σ n tag, ← chase σ n a with
      | (_, .nat 0), (held, .closure _ _) =>
          match ← full σ lim b with
          | some d => pure (some (.waiting held d))
          | none => pure none
      | _, _ => pure none
  | [tag, a] =>
      match ← chase σ n tag with
      | (_, .nat 1) =>
          match ← full σ lim a with
          | some d => pure (some (.finished (.value d)))
          | none => pure none
      | (_, .nat 2) =>
          match ← chase σ n a with
          | (_, .nat i) => pure (some (.finished (.unbound i)))
          | _ => pure none
      | _ => pure none
  | [tag] =>
      match ← chase σ n tag with
      | (_, .nat 3) => pure (some (.finished .wrong))
      | _ => pure none
  | _ => pure none

def openProcs (σ : Store Ref) (n lim : Nat) : List (P Ref) → Except Ref (Option (List (Proc (P Ref) Final)))
  | [] => pure (some [])
  | q :: qs => do
      let some [heldP, statusP] ← parts σ n q | pure none
      let some heldData ← full σ lim heldP | pure none
      let some held := natsOf heldData | pure none
      let some status ← openStatus σ n lim statusP | pure none
      let some rest ← openProcs σ n lim qs | pure none
      pure (some (⟨status, held⟩ :: rest))

/-- `openProcs` with the processes read so far in `acc`, newest first: a loop
    (`homoiconic-q59.78`). -/
def openProcsGo (σ : Store Ref) (n lim : Nat) (acc : List (Proc (P Ref) Final)) :
    List (P Ref) → Except Ref (Option (List (Proc (P Ref) Final)))
  | [] => pure (some acc.reverse)
  | q :: qs => do
      let some [heldP, statusP] ← parts σ n q | pure none
      let some heldData ← full σ lim heldP | pure none
      let some held := natsOf heldData | pure none
      let some status ← openStatus σ n lim statusP | pure none
      openProcsGo σ n lim (⟨status, held⟩ :: acc) qs

theorem openProcsGo_eq (σ : Store Ref) (n lim : Nat) : ∀ (qs : List (P Ref)) (acc : List (Proc (P Ref) Final)),
    openProcsGo σ n lim acc qs = (openProcs σ n lim qs).map (Option.map (acc.reverse ++ ·))
  | [], acc => by simp [openProcsGo, openProcs, pure, Except.pure, Except.map]
  | q :: qs, acc => by
    unfold openProcsGo openProcs
    simp only [bind, Except.bind, pure, Except.pure]
    cases parts σ n q with
    | error r => rfl
    | ok o =>
      simp only []
      split
      · rename_i heldP statusP
        cases full σ lim heldP with
        | error r => rfl
        | ok o2 =>
          simp only []
          cases o2 with
          | none => rfl
          | some hd =>
            simp only []
            cases natsOf hd with
            | none => rfl
            | some held =>
              simp only []
              cases openStatus σ n lim statusP with
              | error r => rfl
              | ok o3 =>
                simp only []
                cases o3 with
                | none => rfl
                | some st =>
                  simp only []
                  rw [openProcsGo_eq σ n lim qs]
                  cases openProcs σ n lim qs with
                  | error r => rfl
                  | ok o4 => cases o4 <;> simp [Except.map]
      · rfl

def openProcsWalk (σ : Store Ref) (n lim : Nat) (qs : List (P Ref)) :
    Except Ref (Option (List (Proc (P Ref) Final))) := openProcsGo σ n lim [] qs

@[csimp] theorem openProcs_eq_walk : @openProcs = @openProcsWalk := by
  funext σ n lim qs
  rw [openProcsWalk, openProcsGo_eq]
  cases openProcs σ n lim qs with
  | error r => rfl
  | ok o => cases o <;> simp [Except.map]

/-- Read a kept node: the identifiers acted on, and the processes. The piece
    must be exactly `[seen, names, processes]`, each process `[held, status]`,
    with names numbers, a payload and a result data, and a waiting program a
    function. As for a VM state, a function's environment is not walked. What
    the piece says a process is waiting on and holds is taken as it is. -/
def openNode (σ : Store Ref) (n lim : Nat) (root : P Ref) : Except Ref (Option (List Data × LConfig)) := do
  let some [seenP, namesP, procsP] ← parts σ n root | pure none
  let some (.arr seen) ← full σ lim seenP | pure none
  let some namesData ← full σ lim namesP | pure none
  let some names := natsOf namesData | pure none
  let some qs ← parts σ n procsP | pure none
  let some procs ← openProcs σ n lim qs | pure none
  pure (some (seen, ⟨procs, names⟩))

/-- Carry the turn on until it is over or needs a piece. For one turn, each
    phase is entered at most once in a call and the phases come in one order;
    a VM goes through them once for each entry it acts on. `fuel` above that
    number is never used up; if it were, the turn says so and is over.
    This follows `Reflect.driveRun` for one turn and `Reflect.vmRun` for a
    log, on the lazy machine. The budget is charged on the lazy machine's
    steps, an operation its cost as on the plain machine (`steps`). There
    are more of those steps than the plain machine's (looking up a variable
    takes steps of its own), so a budget that is enough for `vmRun` may not be
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
          match steps s st with
          | (.paused r st', left, credit) => { s with phase := .run st', left, credit, need := some r }
          | (.full _, _, _) => s.outOfSpace
          | (.at (.halted (.value v)), _, _) => advance fuel { s with phase := .classify v }
          | (.at st', _, _) =>
              match s.node, st' with
              | some _, .halted (.unbound i) =>
                  advance fuel { s with phase := .landed (.finished (.unbound i)) }
              | some _, .halted .wrong =>
                  advance fuel { s with phase := .landed (.finished .wrong) }
              | _, _ => s.stopped st'
      | .classify v =>
          match chase s.store s.reach v with
          | .error r => { s with need := some r }
          | .ok (k, .closure _ _) =>
              -- `k` is the function as it is held: a reference when it was
              -- stored, so that saving it again writes nothing.
              let next := Phase.payload k
                (.running (compile payloadTerm) (.cons k .nil) [] [])
              advance fuel { s with left := s.budget, credit := s.cells, phase := next }
          | .ok (_, d) => advance fuel { s with phase := .result d }
      | .payload k st =>
          match steps s st with
          | (.paused r st', left, credit) => { s with phase := .payload k st', left, credit, need := some r }
          | (.full _, _, _) => s.outOfSpace
          | (.at (.halted (.value p)), _, _) => advance fuel { s with phase := .ask k p }
          | (.at st', _, _) =>
              match s.node, st' with
              | some _, .halted (.unbound i) =>
                  advance fuel { s with phase := .landed (.finished (.unbound i)) }
              | some _, .halted .wrong =>
                  advance fuel { s with phase := .landed (.finished .wrong) }
              | _, _ => s.stopped st'
      | .ask k p =>
          match full s.store s.keepLimit p with
          | .error r => s.stuck r
          | .ok (some d) =>
              match s.node, s.vm with
              | some _, _ => advance fuel { s with phase := .landed (.waiting k d) }
              | none, none => s.wait d k
              | none, some part =>
                  -- `Reflect.handleRun`: an entry whose identifier was acted on
                  -- is passed over, and the next one answers the request.
                  match part.todo.dropWhile (fun e => part.seenSet.contains e.id) with
                  | [] =>
                      s.keepState part s!"waiting on {renderData d}"
                        (.cons (.nat 0) (.cons k .nil))
                  | e :: rest =>
                      let next := Phase.run
                        (.running (compile (resumeTerm e.answer)) (.cons k .nil) [] [])
                      let part := { part with todo := rest, seen := e.id :: part.seen,
                                              seenSet := part.seenSet.insert e.id,
                                              acted := part.acted + 1 }
                      advance fuel { s with left := s.budget, credit := s.cells, vm := some part, phase := next }
          | .ok none =>
              match s.node with
              | some _ => advance fuel { s with phase := .landed (.finished .wrong) }
              | none => s.ended (renderMOutcome .wrong) (.cons (.nat 3) .nil)
      | .result p =>
          match full s.store s.keepLimit p with
          | .error r => s.stuck r
          | .ok (some d) =>
              match s.node with
              | some _ => advance fuel { s with phase := .landed (.finished (.value d)) }
              | none => s.ended (renderData d) (.cons (.nat 1) (.cons d.toP .nil))
          | .ok none => s.finish "error: machine fault"
      | .resuming r d =>
          match s.store r with
          | none => { s with need := some r }
          | some p =>
              -- The root's piece is held as saving would have left it inside
              -- a value: in place when it is small, as its reference when not.
              let first := Phase.run
                (.running (compile (resumeTerm d)) (.cons (opened pieceSize r p) .nil) [] [])
              advance fuel { s with phase := first }
      | .opening root =>
          match openState s.store s.reach s.readLimit root with
          | .error r => s.stuck r
          | .ok none => s.finish "store error: the root is not a kept state"
          | .ok (some (seen, stands)) =>
              let s := { s with vm := s.vm.map (fun (part : VmPart) =>
                { part with seen := seen, seenSet := Std.HashSet.ofList seen }) }
              match stands with
              | .waiting k =>
                  let next := Phase.payload k
                    (.running (compile payloadTerm) (.cons k .nil) [] [])
                  advance fuel { s with left := s.budget, credit := s.cells, phase := next }
              | .value d => advance fuel { s with phase := .result d }
              | .unbound i => s.stopped (.halted (.unbound i))
              | .wrong => s.stopped (.halted .wrong)
      | .openingNode root =>
          match openNode s.store s.reach s.readLimit root, s.node with
          | .error r, _ => s.stuck r
          | .ok (some (seen, cfg)), some part =>
              let part := { part with seen := seen, seenSet := Std.HashSet.ofList seen, cfg := cfg }
              advance fuel { s with node := some part, phase := .step }
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
                      advance fuel { s with left := s.budget, credit := s.cells, node := some part,
                                            phase := .run first }
                  | [] =>
                      match d.done d.got with
                      | none => s.finish "error: the event did not settle"
                      | some cfg =>
                          let part := match d.op with
                            | some o => { part with cfg := cfg, doing := none,
                                                    seen := o.id :: part.seen,
                                                    seenSet := part.seenSet.insert o.id,
                                                    acted := part.acted + 1 }
                            | none => { part with cfg := cfg, doing := none }
                          advance fuel { s with node := some part, phase := .step }
              | none =>
                  -- `Reflect.nodeRun`: an op whose identifier was acted on is
                  -- passed over; the next one happens, or cannot.
                  match part.todo.dropWhile (fun o => part.seenSet.contains o.id) with
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
def start (src : ByteArray) (budget : Nat) (cells : Nat := defaultSpace)
    (count : Option (Phase → PState Ref → Nat) := none) : Session :=
  match Surface.read src with
  | .error msg => failed (renderSyntaxError msg)
  | .ok t =>
      let s : Session := { phase := .run (load (compile t)).toP, budget, left := budget,
                           cells, credit := cells, count }
      advance s.fuel s

/-- Answer the waiting program stored under `root`. The answer is a program
    whose result is the data to give. -/
def answer (root : String) (src : ByteArray) (budget : Nat) (cells : Nat := defaultSpace)
    (count : Option (Phase → PState Ref → Nat) := none) : Session :=
  match unhex root with
  | none => failed "store error: a root is 64 hex digits"
  | some r =>
      match Surface.read src with
      | .error msg => failed ("answer: " ++ renderSyntaxError msg)
      | .ok t =>
          match runTurn budget (load (compile t)) with
          | .halted (.value (.data d)) =>
              let s : Session := { budget, left := budget, phase := .resuming r d,
                                   cells, credit := cells, count }
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
                              fetched := s.fetched + 1, held := s.held + bytes.size,
                              credit := s.credit - bytes.size }
            advance s.fuel s

/-- The name of an entry: the Blake3 hash of its bytes, read as one number,
    first byte highest. That two different entries do not share a name is
    assumed of the hash (D5), and needs `Wire.write` to give different data
    different bytes, which is tested and not proved. -/
def entryName (d : Data) : Data :=
  .nat ((Blake3.hash (write d)).foldl (fun n b => n * 256 + b.toNat) 0)

/-- The identifier of one written entry, after the link in its mark has been
    read. `prev` is `[]` at the first entry and the identifier of the entry
    before it after that. A link's parent must be that, and its order, when
    the mark carries one, must be `k`. The signature is not checked. -/
def acceptMark (prev : Data) (k : Nat) (mark payload : Data) : Except String Data :=
  match readLink mark with
  | none => .ok (entryName (.arr [mark, payload]))
  | some (parent, order) =>
    if parent != prev then .error s!"log: entry {k} does not name the entry before it"
    else match order with
      | some n =>
        if n != k then .error s!"log: entry {k} is out of order"
        else .ok (entryName (.arr [mark, payload]))
      | none => .ok (entryName (.arr [mark, payload]))

/-- The entries of a log given as data, each sealed under `entryName`. -/
def dataEntries (prev : Data) : Nat → List Data → Except String (List Entry)
  | _, [] => .ok []
  | k, .arr [mark, answer] :: ds => do
      let id ← acceptMark prev k mark answer
      let rest ← dataEntries id (k + 1) ds
      pure (⟨id, answer⟩ :: rest)
  | k, _ :: _ => .error s!"log: entry {k} is not a mark and an answer"

/-- `dataEntries` with the entries read so far in `acc`, newest first: a loop
    (`homoiconic-q59.78`; a log of 100000 entries ended the process on a full
    stack). -/
def dataEntriesGo (prev : Data) (k : Nat) (acc : List Entry) : List Data → Except String (List Entry)
  | [] => .ok acc.reverse
  | .arr [mark, answer] :: ds =>
      match acceptMark prev k mark answer with
      | .error m => .error m
      | .ok id => dataEntriesGo id (k + 1) (⟨id, answer⟩ :: acc) ds
  | _ :: _ => .error s!"log: entry {k} is not a mark and an answer"

theorem dataEntriesGo_eq : ∀ (ds : List Data) (prev : Data) (k : Nat) (acc : List Entry),
    dataEntriesGo prev k acc ds = (dataEntries prev k ds).map (acc.reverse ++ ·)
  | [], prev, k, acc => by simp [dataEntriesGo, dataEntries, Except.map]
  | d :: ds, prev, k, acc => by
    by_cases h : ∃ mark answer, d = .arr [mark, answer]
    · obtain ⟨mark, answer, rfl⟩ := h
      rw [dataEntriesGo, dataEntries]
      simp only [bind, Except.bind, pure, Except.pure]
      cases acceptMark prev k mark answer with
      | error m => rfl
      | ok id =>
        simp only []
        rw [dataEntriesGo_eq ds id (k + 1)]
        cases dataEntries id (k + 1) ds <;> simp [Except.map]
    · have h' : ∀ mark answer, d = .arr [mark, answer] → False := fun m e he => h ⟨m, e, he⟩
      rw [dataEntriesGo.eq_3 _ _ _ _ _ h', dataEntries.eq_3 _ _ _ _ h']; rfl

def dataEntriesWalk (prev : Data) (k : Nat) (ds : List Data) : Except String (List Entry) :=
  dataEntriesGo prev k [] ds

@[csimp] theorem dataEntries_eq_walk : @dataEntries = @dataEntriesWalk := by
  funext prev k ds
  rw [dataEntriesWalk, dataEntriesGo_eq]
  cases dataEntries prev k ds <;> simp [Except.map]

/-- Read a log: a program whose result is an array of `[mark, answer]`. -/
def readLog (src : ByteArray) (budget : Nat) : Except String (List Entry) :=
  match Surface.read src with
  | .error msg => .error ("log: " ++ renderSyntaxError msg)
  | .ok t =>
      match runTurn budget (load (compile t)) with
      | .halted (.value (.data (.arr ds))) =>
          match dataEntries (.arr []) 0 ds with
          | .error msg => .error msg
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
                               vm := some { todo := es, given := es.length },
                               cells := turnSpace, credit := turnSpace }
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
                               vm := some { todo := es, given := es.length },
                               cells := turnSpace, credit := turnSpace }
          advance s.fuel s

/-- The ops of a log given as data, each sealed under `entryName`, or the
    place of the first that is not a mark and an event. -/
def dataOps (prev : Data) : Nat → List Data → Except String (List Op)
  | _, [] => .ok []
  | k, .arr [mark, ev] :: ds =>
      match dataEvent ev with
      | none => .error s!"log: entry {k} is not a mark and an event"
      | some e => do
          let id ← acceptMark prev k mark ev
          let rest ← dataOps id (k + 1) ds
          pure (⟨id, e⟩ :: rest)
  | k, _ :: _ => .error s!"log: entry {k} is not a mark and an event"

/-- `dataOps` with the ops read so far in `acc`, newest first: a loop
    (`homoiconic-q59.78`). -/
def dataOpsGo (prev : Data) (k : Nat) (acc : List Op) : List Data → Except String (List Op)
  | [] => .ok acc.reverse
  | .arr [mark, ev] :: ds =>
      match dataEvent ev with
      | none => .error s!"log: entry {k} is not a mark and an event"
      | some e =>
          match acceptMark prev k mark ev with
          | .error m => .error m
          | .ok id => dataOpsGo id (k + 1) (⟨id, e⟩ :: acc) ds
  | _ :: _ => .error s!"log: entry {k} is not a mark and an event"

theorem dataOpsGo_eq : ∀ (ds : List Data) (prev : Data) (k : Nat) (acc : List Op),
    dataOpsGo prev k acc ds = (dataOps prev k ds).map (acc.reverse ++ ·)
  | [], prev, k, acc => by simp [dataOpsGo, dataOps, Except.map]
  | d :: ds, prev, k, acc => by
    by_cases h : ∃ mark ev, d = .arr [mark, ev]
    · obtain ⟨mark, ev, rfl⟩ := h
      rw [dataOpsGo, dataOps]
      cases dataEvent ev with
      | none => rfl
      | some e =>
        simp only [bind, Except.bind, pure, Except.pure]
        cases acceptMark prev k mark ev with
        | error m => rfl
        | ok id =>
          simp only []
          rw [dataOpsGo_eq ds id (k + 1)]
          cases dataOps id (k + 1) ds <;> simp [Except.map]
    · have h' : ∀ mark ev, d = .arr [mark, ev] → False := fun m e he => h ⟨m, e, he⟩
      rw [dataOpsGo.eq_3 _ _ _ _ _ h', dataOps.eq_3 _ _ _ _ h']; rfl

def dataOpsWalk (prev : Data) (k : Nat) (ds : List Data) : Except String (List Op) :=
  dataOpsGo prev k [] ds

@[csimp] theorem dataOps_eq_walk : @dataOps = @dataOpsWalk := by
  funext prev k ds
  rw [dataOpsWalk, dataOpsGo_eq]
  cases dataOps prev k ds <;> simp [Except.map]

/-- Read a node's log: a program whose result is an array of
    `[mark, event]`. -/
def readOps (src : ByteArray) (budget : Nat) : Except String (List Op) :=
  match Surface.read src with
  | .error msg => .error ("log: " ++ renderSyntaxError msg)
  | .ok t =>
      match runTurn budget (load (compile t)) with
      | .halted (.value (.data (.arr ds))) =>
          match dataOps (.arr []) 0 ds with
          | .error msg => .error msg
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
                                              doing := some first },
                               cells := turnSpace, credit := turnSpace }
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
                               node := some { todo := os, given := os.length },
                               cells := turnSpace, credit := turnSpace }
          advance s.fuel s

end Surface.Keep
