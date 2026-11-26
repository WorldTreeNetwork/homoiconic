import Surface.Chan
import Surface.Keep
import Reflect.Crossing
import Reflect.Hold
import Wire.Form
import Wire.Blake3

/-!
A guest of a run on two machines, and the check of what two guests recorded.

A guest holds its own processes and runs them with the measured channel runs
(`Reflect.stepMade`, `turnMade`, `settleMade`, `beginMade`), which give what
`stepIn`, `turnIn`, `settleIn` and `beginIn` give and the cells they made,
each machine run with the step budget and the turn space the two guests
agreed on. A start or a send whose other process is on the peer is a
*crossing*: it is put out as a packet, taken in on the other guest, and
acknowledged. Each thing a guest does is a `Reflect.Note` in its log.

A guest's budgets are its own (`harden-crossing`, D-1): a step limit and a
turn limit given at its start, lowered by what the peer announces before the
guest runs anything, never raised. What it holds is bounded by a ledger
(D-2): each entry is charged what it made (`Reflect.Hold`), and when the
credit is spent the guest counts what it holds and records `held m` or, past
three quarters of its hold or at a cap, `full m`, and stops.

`check` reads two records, combines the logs (`Reflect.combineTrace`),
requires each guest's acknowledgements in the order the other took its
crossings, replays the schedule on one machine charging each entry as its
guest did (`Reflect.traceRun`), walks each side's ledger
(`Reflect.holdWalk`), and compares each process with the line its guest
reported, a digest of its state among it.

What a guest does is tested, not proved. Of the check it is proved that an
accepted record is a run of the one-machine network (`accepted_network`,
`traceRun_sched`) and what the ledger walk accepts (`hold_stretch` and its
relatives).
-/
namespace Surface.Cross
open Reflect

def noteData : Note → Data
  | .did ev => .arr [.nat 0, eventData ev]
  | .out i k => .arr [.nat 1, .nat i, .nat k]
  | .spawnIn k => .arr [.nat 2, .nat k]
  | .sendIn k j => .arr [.nat 3, .nat k, .nat j]
  | .ack k i => .arr [.nat 4, .nat k, .nat i]
  | .held m => .arr [.nat 5, .nat m]
  | .full m => .arr [.nat 6, .nat m]

def dataNote : Data → Option Note
  | .arr [.nat 0, d] => (dataEvent d).map .did
  | .arr [.nat 1, .nat i, .nat k] => some (.out i k)
  | .arr [.nat 2, .nat k] => some (.spawnIn k)
  | .arr [.nat 3, .nat k, .nat j] => some (.sendIn k j)
  | .arr [.nat 4, .nat k, .nat i] => some (.ack k i)
  | .arr [.nat 5, .nat m] => some (.held m)
  | .arr [.nat 6, .nat m] => some (.full m)
  | _ => none

/-- A guest's own step limit when it is given none: the most a run frame may
    ask (`budget_max` in `unikernel/net.zig`). -/
def defaultLimit : Nat := 100000000
/-- A guest's own turn space when it is given none. -/
def defaultTurn : Nat := 500000
/-- A guest's own hold when it is given none. -/
def defaultHold : Nat := 2000000
/-- The most hold a check walks. -/
def checkHold : Nat := 64000000

/-- A process that asked for a crossing and is held: its place, the crossing,
    and where its turn on `[]` leaves it, run before the request left. -/
structure Asked where
  place : Nat
  k : Nat
  next : Status MValue MOutcome

/-- A send of the peer's that has arrived and has not been taken. -/
structure Pending where
  k : Nat
  name : Nat
  message : Data
  held : List Nat

structure Guest where
  /-- `a` is the guest that is given the program. -/
  side : Side
  /-- This guest opens the exchanges, and closes the run. -/
  caller : Bool
  /-- Its own most steps for a machine run, and cells for a turn. -/
  limit : Nat
  turnLimit : Nat
  /-- Its own bound on what it holds, in cells. -/
  hold : Nat
  /-- The steps and the cells every machine run gets: its own, lowered by the
      program's frame and by what the peer announced until `fixed`. -/
  budget : Nat
  cells : Nat
  /-- The guest has run something; its budgets no longer change. -/
  fixed : Bool := false
  /-- A batch from the peer was taken. Side `a` begins only after one. -/
  heard : Bool := false
  /-- Side `a` before it begins its program. -/
  waiting : Bool := false
  /-- The program, given and not yet begun. -/
  program : Option Term := none
  /-- Every start request goes to the peer. -/
  far : Bool
  /-- Among the peer's sends that can be taken, take the newest first. -/
  takeNew : Bool
  cfg : MConfig := ⟨[], []⟩
  /-- Names made here. -/
  made : Nat := 0
  /-- Crossings put out here. -/
  outs : Nat := 0
  asked : List Asked := []
  /-- Processes whose next run did not finish within the budget. -/
  stuck : List Nat := []
  /-- Packets accepted and not yet worked, oldest first. -/
  inbox : List Data := []
  pending : List Pending := []
  /-- Newest first. -/
  log : List Note := []
  logLength : Nat := 0
  /-- The packets sent that the peer has not counted, oldest first; the
      first is number `sentBase`. A list: the runtime's count does not look
      inside an array. -/
  sent : List Data := []
  sentBase : Nat := 0
  /-- How many of the peer's packets were accepted. -/
  got : Nat := 0
  /-- What the ledger has left. -/
  credit : Nat
  /-- The guest counted more than three quarters of its hold, or reached a
      cap, and stopped. -/
  full : Bool := false
  /-- `work` found nothing possible. -/
  resting : Bool := false
  /-- The peer's last batch said it was idle and carried no packet. -/
  peerQuiet : Bool := false
  closed : Bool := false
  error : String := ""

/-- The most bytes one crossing's packet may have. -/
def packetLimit : Nat := 6000

/-- The most of the peer's packets a guest queues: an honest peer has at most
    `outLimit` crossings out and owes at most `outLimit` acknowledgements. -/
def queueLimit : Nat := 2 * outLimit

/-- A count that always answers "too many": the ledger is all the guest has
    (as `Space.ledger`). For guests run where the runtime cannot count. -/
def ledgerCount (g : Guest) : Nat := g.hold + 1

def Guest.post (g : Guest) (pkt : Data) : Guest := { g with sent := g.sent ++ [pkt] }

/-- Record an entry charged `cost`. When the cost passes what is left of the
    credit, or the log or the processes reach a cap, count what the guest
    holds and record it at once: `held m`, and the credit is the hold less
    `m`; or, past three quarters of the hold or at a cap, `full m`. Nothing
    is charged after `full`. -/
def Guest.note (count : Guest → Nat) (g : Guest) (n : Note) (cost : Nat) : Guest :=
  let g := { g with log := n :: g.log, logLength := g.logLength + 1 }
  if g.full then g else
  let cap := entryLimit ≤ g.logLength || procLimit ≤ g.cfg.procs.length
  if cost ≤ g.credit && !cap then { g with credit := g.credit - cost } else
  let m := count g
  let g := { g with log := (if !cap && m ≤ holdBar g.hold then .held m else .full m) :: g.log,
                    logLength := g.logLength + 1 }
  if !cap && m ≤ holdBar g.hold then { g with credit := g.hold - m }
  else { g with full := true }

/-- The process waits to send on a name it holds. -/
def wantsSend (q : Proc MValue MOutcome) : Bool :=
  match q.status with
  | .waiting _ p =>
    match classify p with
    | .send ch _ => q.held.contains ch
    | _ => false
  | _ => false

/-- The process waits on a start request. -/
def wantsSpawn (q : Proc MValue MOutcome) : Bool :=
  match q.status with
  | .waiting _ p =>
    match classify p with
    | .spawn _ _ => true
    | _ => false
  | _ => false

/-- The guest makes no more packets until the peer counts some, or has as
    many crossings out as it may. -/
def Guest.outFull (g : Guest) : Bool := outLimit ≤ g.asked.length || queueLimit ≤ g.sent.length

/-- The configuration with every held or stuck process hidden, so that the
    scheduler neither chooses it nor finds it as a partner; and, while the
    guest may put nothing out, every start it would put out. -/
def Guest.masked (g : Guest) : MConfig :=
  ⟨g.cfg.procs.mapIdx fun i q =>
      if g.asked.any (·.place == i) || g.stuck.contains i || (g.far && g.outFull && wantsSpawn q)
      then ⟨.finished .wrong, []⟩ else q,
    g.cfg.names⟩

/-! What a guest does. -/

def numbers : List Data → Option (List Nat)
  | [] => some []
  | .nat n :: ds => (numbers ds).map (n :: ·)
  | _ :: _ => none

/-- `numbers`, as a loop over the list (`homoiconic-q59.72`). -/
def numbersGo (acc : List Nat) : List Data → Option (List Nat)
  | [] => some acc.reverse
  | .nat n :: ds => numbersGo (n :: acc) ds
  | _ :: _ => none

theorem numbersGo_eq (acc : List Nat) (ds : List Data) :
    numbersGo acc ds = (numbers ds).map (acc.reverse ++ ·) := by
  induction ds generalizing acc with
  | nil => simp [numbersGo, numbers]
  | cons d ds ih =>
    cases d <;> simp [numbersGo, numbers, ih, Function.comp_def]

def numbersWalk (ds : List Data) : Option (List Nat) := numbersGo [] ds

@[csimp] theorem numbers_eq_walk : @numbers = @numbersWalk := by
  funext ds; simp [numbersWalk, numbersGo_eq]


section
variable (count : Guest → Nat)

/-- Work one packet from the peer. A full guest takes only acknowledgements.
    A start waits while the guest may make no packet. -/
def Guest.takeIn (g : Guest) : Option Guest :=
  match g.inbox with
  | [] => none
  | pkt :: rest =>
    match pkt with
    | .arr [.nat 0, .nat k, prog, start, .arr held] =>
      if !g.full && queueLimit ≤ g.sent.length then none else
      let g : Guest := { g with inbox := rest, fixed := true }
      if g.full then some g else
      match unreify prog, numbers held with
      | some t, some hs =>
        let r := runTurnMade g.cells g.budget (load (compile (.app t (.lit start))))
        match r.1 with
        | .halted w =>
          let ch := settleMade g.cells g.budget w
          match ch.1 with
          | some child =>
            let cfg : MConfig := ⟨g.cfg.procs ++ [⟨child, hs⟩], g.cfg.names⟩
            some ((({ g with cfg }).post (ackPacket k)).note count (.spawnIn k)
              (takeCharge k pkt (r.2 + ch.2)))
          | none => some g
        | _ => some g
      | _, _ => some g
    | .arr [.nat 1, .nat k, .nat name, message, .arr held] =>
      let g : Guest := { g with inbox := rest, fixed := true }
      if g.full then some g else
      match numbers held with
      | some hs => some { g with pending := g.pending ++ [⟨k, name, message, hs⟩] }
      | none => some g
    | .arr [.nat 2, .nat k] =>
      let g : Guest := { g with inbox := rest, fixed := true }
      match g.asked.find? (·.k == k) with
      | some a =>
        match g.cfg.procs[a.place]? with
        | some q =>
          let cfg : MConfig := ⟨g.cfg.procs.set a.place ⟨a.next, q.held⟩, g.cfg.names⟩
          some (({ g with cfg, asked := g.asked.filter (·.k != k) }).note count (.ack k a.place)
            entryCells)
        | none => some g
      | none => some g
    | _ => some { g with inbox := rest }

/-- Take one of the peer's pending sends that a local receiver can take: the
    oldest, or the newest with `takeNew`. -/
def Guest.takeSend (g : Guest) : Option Guest :=
  if g.full || queueLimit ≤ g.sent.length then none else
  let m := g.masked
  let able := g.pending.filter fun p => (findProc (receivesOn p.name) m.procs).isSome
  match (if g.takeNew then able.getLast? else able.head?) with
  | none => none
  | some p =>
    let g : Guest := { g with pending := g.pending.filter (·.k != p.k) }
    match findProc (receivesOn p.name) m.procs with
    | some j =>
      match g.cfg.procs[j]? with
      | some ⟨.waiting c _, held⟩ =>
        let r := turnMade g.cells g.budget c p.message
        match r.1 with
        | some st =>
          let cfg : MConfig := ⟨g.cfg.procs.set j ⟨st, gain held p.held⟩, g.cfg.names⟩
          let pkt : Data := .arr [.nat 1, .nat p.k, .nat p.name, p.message, .arr (p.held.map .nat)]
          some ((({ g with cfg }).post (ackPacket p.k)).note count (.sendIn p.k j)
            (takeCharge p.k pkt r.2))
        | none => some g
      | _ => some g
    | none => some g

/-- Put process `i`'s start or send out to the peer. Its turn on `[]` is run
    first and kept; when that does not finish nothing leaves. -/
def Guest.ask (g : Guest) (i : Nat) : Option Guest :=
  if g.outFull then none else
  match g.cfg.procs[i]? with
  | some ⟨.waiting c p, held⟩ =>
    match packetOf g.outs held p with
    | some pkt =>
      if (Wire.write pkt).size > packetLimit then some { g with stuck := i :: g.stuck } else
      let r := turnMade g.cells g.budget c (.arr [])
      match r.1 with
      | some next =>
        some ((({ g with asked := ⟨i, g.outs, next⟩ :: g.asked, outs := g.outs + 1 }).post pkt).note
          count (.out i g.outs) (outCharge r.2 pkt))
      | none => some { g with stuck := i :: g.stuck }
    | none => none
  | _ => none

/-- A local event `ev` of process `i`, run as one machine runs it. -/
def Guest.happen (g : Guest) (i : Nat) (ev : Event) : Guest :=
  let r := stepMade g.cells g.budget g.cfg ev
  match r.1 with
  | .ok cfg => ({ g with cfg }).note count (.did ev) (didCharge g.cfg ev r.2.1 r.2.2)
  | _ => { g with stuck := i :: g.stuck }

/-- One local event, or one request put out. A new channel is named by the
    guest's side, even on `a` and odd on `b`, not by `pick`. -/
def Guest.act (g : Guest) : Option Guest :=
  if g.full then none else
  let m := g.masked
  match pick m with
  | some (.fresh i _) =>
    let n := 2 * g.made + (if g.side = .a then 0 else 1)
    some ({ g with made := g.made + 1 }.happen count i (.fresh i n))
  | some (.spawn i) => if g.far then g.ask count i else some (g.happen count i (.spawn i))
  | some (.comm i j) => some (g.happen count i (.comm i j))
  | some (.answer _ _) => none
  | none =>
    match findProc wantsSend m.procs with
    | some i => g.ask count i
    | none => none

/-- Side `a` begins its program once it has it and has heard the peer. What
    beginning made is charged first. -/
def Guest.begin (g : Guest) : Option Guest :=
  if !g.waiting || !g.heard then none else
  match g.program with
  | none => none
  | some t =>
    let r := beginMade g.cells g.budget t
    match r.1 with
    | some cfg =>
      let first := beginCharge (reify t) r.2
      let g := { g with cfg, waiting := false, program := none, fixed := true, resting := false }
      if first ≤ g.hold then some { g with credit := g.hold - first } else
      let m := count g
      let g := { g with credit := 0, logLength := 1,
                        log := [if m ≤ holdBar g.hold then .held m else .full m] }
      if m ≤ holdBar g.hold then some { g with credit := g.hold - m } else some { g with full := true }
    | none => some { g with error := s!"no result within {g.budget} steps of a turn" }

def Guest.step (g : Guest) : Option Guest :=
  match g.begin count with
  | some g => some g
  | none =>
    match g.takeIn count with
    | some g => some g
    | none =>
      match g.takeSend count with
      | some g => some g
      | none => g.act count

/-- Work until nothing is possible, or `limit` steps. -/
def Guest.work : Nat → Guest → Guest
  | 0, g => g
  | limit + 1, g =>
    match g.step count with
    | some g' => Guest.work limit g'
    | none => { g with resting := true }

end

def workLimit : Nat := 256

/-- Nothing to do and nothing the peer has not counted. A guest that still
    waits to begin its program is not idle. -/
def Guest.idle (g : Guest) : Bool :=
  !g.waiting && g.resting && g.inbox.isEmpty && g.sent.isEmpty

/-- The guest that opens the exchanges closes when it is idle and the peer's
    last batch was quiet. The other closes when told. -/
def Guest.closing (g : Guest) : Bool :=
  g.closed || (g.caller && g.idle && g.peerQuiet)

/-- The batch for the peer: a flag, how many of its packets were accepted, the
    steps and the cells this guest runs with as they stand, and the packets
    the peer has not counted, as many as fit in `room` bytes. -/
def Guest.batch (g : Guest) (room : Nat) : ByteArray :=
  let flag := if g.closing then 2 else if g.idle then 1 else 0
  let pkts := g.sent.foldl (fun (acc : List Data × Nat × Bool × Nat) pkt =>
    let size := (Wire.write pkt).size + 16
    if acc.2.2.1 || acc.2.1 + size > room then (acc.1, acc.2.1, true, acc.2.2.2 + 1)
    else (acc.1 ++ [.arr [.nat acc.2.2.2, pkt]], acc.2.1 + size, false, acc.2.2.2 + 1))
    ([], 64, false, g.sentBase)
  Wire.write (.arr [.nat flag, .nat g.got, .nat g.budget, .nat g.cells, .arr pkts.1])

/-- Take a batch from the peer. Packets are only queued here, at most
    `queueLimit` of them; one past that is not counted and comes again. Until
    the guest has run anything, the peer's numbers lower its own. -/
def Guest.take (g : Guest) (bytes : ByteArray) : Guest :=
  match Wire.read bytes with
  | .ok (.arr [.nat flag, .nat got, .nat steps, .nat cells, .arr pkts]) =>
    let counted := min got (g.sentBase + g.sent.length)
    let g := { g with sent := g.sent.drop (counted - g.sentBase),
                      sentBase := max g.sentBase counted,
                      peerQuiet := flag ≥ 1 && pkts.isEmpty,
                      heard := true,
                      budget := if g.fixed then g.budget else min g.budget steps,
                      cells := if g.fixed then g.cells else min g.cells cells }
    let g := pkts.foldl (fun (g : Guest) p =>
      match p with
      | .arr [.nat seq, pkt] =>
        if seq == g.got && g.inbox.length + g.pending.length < queueLimit then
          { g with inbox := g.inbox ++ [pkt], got := g.got + 1, resting := false }
        else g
      | _ => g) g
    if flag == 2 then { g with closed := true } else g
  | _ => g

/-- Begin a guest with no process, with its own step limit, turn limit and
    hold. The guest that will be given the program is side `a`, and waits
    for it. -/
def start (hasProgram caller far takeNew : Bool) (limit turn hold : Nat) : Guest :=
  { side := if hasProgram then .a else .b, caller, far, takeNew, waiting := hasProgram,
    limit, turnLimit := turn, hold, budget := limit, cells := turn, credit := hold }

/-- Give the waiting guest its program, in its byte form, and the step budget
    it came with, which can only lower the guest's own. It is begun as the
    first process once the guest has heard the peer. -/
def Guest.give (g : Guest) (program : ByteArray) (budget : Nat) : Guest :=
  if !g.waiting || g.program.isSome then g else
  match Wire.readProgram program with
  | .error msg => { g with error := "bytes error: " ++ msg }
  | .ok t => { g with program := some t, resting := false,
                      budget := if g.fixed then g.budget else min g.budget budget }

/-- 0: there is work. 1: resting. 2: closed. 3: failed. -/
def Guest.state (g : Guest) : UInt8 :=
  if g.error != "" then 3 else if g.closed then 2
  else if (g.waiting && (g.program.isNone || !g.heard)) || (g.resting && g.inbox.isEmpty) then 1
  else 0

/-! The record. -/

/-- The written entries of a log, oldest first, each `[mark, body]` with the
    mark `[0, parent, order]`, and the name of the last. -/
def chain (prev : Data) : Nat → List Data → List Data × Data
  | _, [] => ([], prev)
  | k, body :: bodies =>
    let e := Data.arr [.arr [.nat 0, prev, .nat k], body]
    let r := chain (Keep.entryName e) (k + 1) bodies
    (e :: r.1, r.2)

/-- `chain`, with the entries written so far kept newest first: one call for
    each entry is a loop, however long the log grows (`homoiconic-q59.72`). -/
def chainGo (acc : List Data) (prev : Data) : Nat → List Data → List Data × Data
  | _, [] => (acc.reverse, prev)
  | k, body :: bodies =>
    let e := Data.arr [.arr [.nat 0, prev, .nat k], body]
    chainGo (e :: acc) (Keep.entryName e) (k + 1) bodies

theorem chainGo_eq (acc : List Data) (prev : Data) (k : Nat) (bodies : List Data) :
    chainGo acc prev k bodies = (acc.reverse ++ (chain prev k bodies).1, (chain prev k bodies).2) := by
  induction bodies generalizing acc prev k with
  | nil => simp [chainGo, chain]
  | cons b bs ih => simp [chainGo, chain, ih]

def chainWalk (prev : Data) (k : Nat) (bodies : List Data) : List Data × Data :=
  chainGo [] prev k bodies

@[csimp] theorem chain_eq_walk : @chain = @chainWalk := by
  funext prev k bodies; simp [chainWalk, chainGo_eq]

/-- The most of a payload or a result a line prints, and the most names. -/
def lineRoom : Nat := 512
def namesShown : Nat := 32
/-- The room for one process's root and for a side's digests, in units of
    `Wire.valuesFit`. -/
def procRoom : Nat := 4000000
def sideRoom : Nat := 64000000

def heldData (held : List Nat) : Data := .arr (held.map .name)

/-- The machine values whose data form is a process's state: its names, and
    its function and payload, or its result. -/
def stateValues (q : Proc MValue MOutcome) : List MValue :=
  .data (heldData q.held) ::
    match q.status with
    | .waiting c p => [c, .data p]
    | .finished (.value v) => [v]
    | .finished _ => []

/-- The state as data: `[names, [0, function, payload]]`, `[names, [1, value]]`,
    `[names, [2, i]]`, `[names, [3]]`. -/
def stateForm (q : Proc MValue MOutcome) : Option Data :=
  let status : Option Data :=
    match q.status with
    | .waiting c p => (Wire.valueData c).map fun d => .arr [.nat 0, d, p]
    | .finished (.value v) => (Wire.valueData v).map fun d => .arr [.nat 1, d]
    | .finished (.unbound i) => some (.arr [.nat 2, .nat i])
    | .finished .wrong => some (.arr [.nat 3])
  status.map fun s => .arr [heldData q.held, s]

/-- The state as data with a function left out: `[names, [0, payload]]`,
    `[names, [1, data]]`, `[names, [1]]` for a function, and as above. -/
def stateData (q : Proc MValue MOutcome) : Data :=
  .arr [heldData q.held,
    match q.status with
    | .waiting _ p => .arr [.nat 0, p]
    | .finished (.value (.data d)) => .arr [.nat 1, d]
    | .finished (.value (.closure _ _)) => .arr [.nat 1]
    | .finished (.unbound i) => .arr [.nat 2, .nat i]
    | .finished .wrong => .arr [.nat 3]]

def digestOf (d : Data) : String := Keep.hex (Wire.Blake3.hash (Wire.write d))

/-- A process's digest, and the room left: `root` of its state when its form
    fits in `procRoom` and what is left, else `data` of its state without the
    function when that fits in what is left after `procRoom`, else `root none`. -/
def digest (q : Proc MValue MOutcome) (left : Nat) : String × Nat :=
  let try1 := min procRoom left
  let root : Option (String × Nat) :=
    match Wire.valuesFit try1 [] (stateValues q) with
    | some rest => (stateForm q).map fun d => ("root " ++ digestOf d, left - (try1 - rest))
    | none => none
  match root with
  | some r => r
  | none =>
    let left := left - try1
    let d := stateData q
    match Wire.valuesFit left [] [.data d] with
    | some rest => ("data " ++ digestOf d, rest)
    | none => ("root none", 0)

def statusText (q : Proc MValue MOutcome) : String :=
  match q.status with
  | .waiting _ p =>
    if p.writes lineRoom then "waiting on " ++ renderData p else s!"waiting on more than {lineRoom} written"
  | .finished (.value (.data d)) =>
    if d.writes lineRoom then renderData d else s!"more than {lineRoom} written"
  | .finished w => renderMOutcome w

def namesText (held : List Nat) : String :=
  if held.length ≤ namesShown then renderData (heldData held) else s!"{held.length} names"

/-- The lines of a side's processes, in local order, with the side's room for
    digests used in that order. -/
def procLines (qs : List (Proc MValue MOutcome)) : List String :=
  (qs.foldl (fun (acc : List String × Nat) q =>
    let d := digest q acc.2
    ((statusText q ++ "; holds " ++ namesText q.held ++ "; " ++ d.1) :: acc.1, d.2))
    ([], sideRoom)).1.reverse

def recordText (me peer : String) (budget own : List Nat) (bodies : List Data) (procs : List String) :
    String :=
  let s := chain (.arr []) 0 bodies
  s!"form 2\nme {me}\npeer {peer}\n" ++
    "budget " ++ " ".intercalate (budget.map toString) ++ "\n" ++
    "own " ++ " ".intercalate (own.map toString) ++ "\n" ++
    String.join (s.1.map fun e => "entry " ++ renderData e ++ "\n") ++
    s!"head {s.1.length} " ++ renderData s.2 ++ "\n" ++
    String.join (procs.map fun l => "proc " ++ l ++ "\n")

/-- What a guest hands over: its name, its peer's, the budgets it ran with and
    its own, its log, the head, and a line for each of its processes. -/
def Guest.record (g : Guest) (me peer : String) : String :=
  if g.error != "" then "error " ++ g.error ++ "\n" else
  recordText me peer [g.budget, g.cells] [g.limit, g.turnLimit, g.hold]
    (g.log.reverse.map noteData) (procLines g.cfg.procs)

structure Record where
  form : Bool := false
  me : String := ""
  peer : String := ""
  budget : List Nat := []
  own : List Nat := []
  entries : List Data := []
  head : Option (Nat × Data) := none
  procs : List String := []

/-- Read one written data value. -/
def readData (s : String) : Option Data :=
  match Surface.read s.toUTF8 with
  | .error _ => none
  | .ok t =>
    match runTurn 10000000 (load (compile t)) with
    | .halted (.value (.data d)) => some d
    | _ => none

/-- A record's number: at most 20 digits, so that reading it takes no time to
    speak of whatever a record holds (`homoiconic-q59.82`). -/
def numberWord (w : String) : Option Nat := if w.length ≤ 20 then w.toNat? else none

def numbersText (s : String) : Option (List Nat) :=
  (s.splitOn " ").foldr (fun w acc => match numberWord w, acc with
    | some n, some ns => some (n :: ns)
    | _, _ => none) (some [])

def readLines (who : String) : Nat → List String → Record → Except String Record
  | _, [], r => .ok r
  | k, l :: ls, r =>
    if l == "" then readLines who (k + 1) ls r
    else if l == "form 2" then readLines who (k + 1) ls { r with form := true }
    else if l.startsWith "me " then readLines who (k + 1) ls { r with me := (l.drop 3).toString }
    else if l.startsWith "peer " then readLines who (k + 1) ls { r with peer := (l.drop 5).toString }
    else if l.startsWith "budget " then
      match numbersText (l.drop 7).toString with
      | some [s, c] => readLines who (k + 1) ls { r with budget := [s, c] }
      | _ => .error s!"record {who}: line {k} is not read"
    else if l.startsWith "own " then
      match numbersText (l.drop 4).toString with
      | some [s, c, h] => readLines who (k + 1) ls { r with own := [s, c, h] }
      | _ => .error s!"record {who}: line {k} is not read"
    else if l.startsWith "entry " then
      match readData (l.drop 6).toString with
      | some d => readLines who (k + 1) ls { r with entries := r.entries ++ [d] }
      | none => .error s!"record {who}: line {k} is not read"
    else if l.startsWith "head " then
      match ((l.drop 5).toString.splitOn " ") with
      | [n, name] =>
        match numberWord n, readData name with
        | some n, some d => readLines who (k + 1) ls { r with head := some (n, d) }
        | _, _ => .error s!"record {who}: line {k} is not read"
      | _ => .error s!"record {who}: line {k} is not read"
    else if l.startsWith "proc " then
      readLines who (k + 1) ls { r with procs := r.procs ++ [(l.drop 5).toString] }
    else .error s!"record {who}: line {k} is not read"

/-- `r` with the entries and the process lines read since it was last set,
    each list newest first, put after its own. -/
def Record.with (r : Record) (es : List Data) (ps : List String) : Record :=
  { r with entries := r.entries ++ es.reverse, procs := r.procs ++ ps.reverse }

/-- `readLines` with the entries and process lines read so far kept newest
    first and put in order once at the end, so reading a record takes time
    linear in its lines, not quadratic (`homoiconic-q59.78`). -/
def readLinesGo (who : String) : Nat → List String → Record → List Data → List String →
    Except String Record
  | _, [], r, es, ps => .ok (r.with es ps)
  | k, l :: ls, r, es, ps =>
    if l == "" then readLinesGo who (k + 1) ls r es ps
    else if l == "form 2" then readLinesGo who (k + 1) ls { r with form := true } es ps
    else if l.startsWith "me " then readLinesGo who (k + 1) ls { r with me := (l.drop 3).toString } es ps
    else if l.startsWith "peer " then readLinesGo who (k + 1) ls { r with peer := (l.drop 5).toString } es ps
    else if l.startsWith "budget " then
      match numbersText (l.drop 7).toString with
      | some [s, c] => readLinesGo who (k + 1) ls { r with budget := [s, c] } es ps
      | _ => .error s!"record {who}: line {k} is not read"
    else if l.startsWith "own " then
      match numbersText (l.drop 4).toString with
      | some [s, c, h] => readLinesGo who (k + 1) ls { r with own := [s, c, h] } es ps
      | _ => .error s!"record {who}: line {k} is not read"
    else if l.startsWith "entry " then
      match readData (l.drop 6).toString with
      | some d => readLinesGo who (k + 1) ls r (d :: es) ps
      | none => .error s!"record {who}: line {k} is not read"
    else if l.startsWith "head " then
      match ((l.drop 5).toString.splitOn " ") with
      | [n, name] =>
        match numberWord n, readData name with
        | some n, some d => readLinesGo who (k + 1) ls { r with head := some (n, d) } es ps
        | _, _ => .error s!"record {who}: line {k} is not read"
      | _ => .error s!"record {who}: line {k} is not read"
    else if l.startsWith "proc " then
      readLinesGo who (k + 1) ls r es ((l.drop 5).toString :: ps)
    else .error s!"record {who}: line {k} is not read"

theorem readLinesGo_eq (who : String) : ∀ (ls : List String) (k : Nat) (r : Record)
    (es : List Data) (ps : List String),
    readLinesGo who k ls r es ps = readLines who k ls (r.with es ps)
  | [], k, r, es, ps => by simp [readLinesGo, readLines]
  | l :: ls, k, r, es, ps => by
    have ih := readLinesGo_eq who ls (k + 1)
    rw [readLinesGo, readLines]
    by_cases h : (l == "") = true
    · rw [if_pos h, if_pos h]
      exact ih _ _ _
    rw [if_neg h, if_neg h]
    by_cases h : (l == "form 2") = true
    · rw [if_pos h, if_pos h]
      exact ih _ _ _
    rw [if_neg h, if_neg h]
    by_cases h : (l.startsWith "me ") = true
    · rw [if_pos h, if_pos h]
      exact ih _ _ _
    rw [if_neg h, if_neg h]
    by_cases h : (l.startsWith "peer ") = true
    · rw [if_pos h, if_pos h]
      exact ih _ _ _
    rw [if_neg h, if_neg h]
    by_cases h : (l.startsWith "budget ") = true
    · rw [if_pos h, if_pos h]
      split
      · exact ih _ _ _
      · rfl
    rw [if_neg h, if_neg h]
    by_cases h : (l.startsWith "own ") = true
    · rw [if_pos h, if_pos h]
      split
      · exact ih _ _ _
      · rfl
    rw [if_neg h, if_neg h]
    by_cases h : (l.startsWith "entry ") = true
    · rw [if_pos h, if_pos h]
      split
      · rw [ih]; congr 1; simp [Record.with]
      · rfl
    rw [if_neg h, if_neg h]
    by_cases h : (l.startsWith "head ") = true
    · rw [if_pos h, if_pos h]
      split
      · split
        · exact ih _ _ _
        · rfl
      · rfl
    rw [if_neg h, if_neg h]
    by_cases h : (l.startsWith "proc ") = true
    · rw [if_pos h, if_pos h]
      rw [ih]; congr 1; simp [Record.with]
    rw [if_neg h, if_neg h]

def readLinesWalk (who : String) (k : Nat) (ls : List String) (r : Record) : Except String Record :=
  readLinesGo who k ls r [] []

@[csimp] theorem readLines_eq_walk : @readLines = @readLinesWalk := by
  funext who k ls r
  rw [readLinesWalk, readLinesGo_eq]
  simp [Record.with]

def readRecord (who : String) (bytes : ByteArray) : Except String Record := do
  match String.fromUTF8? bytes with
  | none => .error s!"record {who}: not text"
  | some s =>
    let r ← readLines who 0 (s.splitOn "\n") {}
    if !r.form then .error s!"record {who}: not of form 2"
    else if r.budget.length != 2 || r.own.length != 3 then .error s!"record {who}: a line is missing"
    else pure r

/-- Read the chain: every mark is `[0, parent, order]`, its parent the entry
    before it and its order its place. Gives the notes and the name of the
    last entry. -/
def readChain (who : String) (prev : Data) : Nat → List Data → Except String (List Note × Data)
  | _, [] => .ok ([], prev)
  | k, .arr [.arr [.nat 0, parent, .nat n], body] :: ds =>
    if parent != prev then .error s!"log {who}: entry {k} does not name the entry before it"
    else if n != k then .error s!"log {who}: entry {k} is out of order"
    else
      match dataNote body with
      | none => .error s!"log {who}: entry {k} is not an entry"
      | some note => do
        let r ← readChain who (Keep.entryName (.arr [.arr [.nat 0, parent, .nat n], body])) (k + 1) ds
        pure (note :: r.1, r.2)
  | k, _ :: _ => .error s!"log {who}: entry {k} has no link"

/-- `readChain` with the notes read so far in `acc`, newest first: a loop
    (`homoiconic-q59.78`). -/
def readChainGo (who : String) (acc : List Note) (prev : Data) : Nat → List Data →
    Except String (List Note × Data)
  | _, [] => .ok (acc.reverse, prev)
  | k, .arr [.arr [.nat 0, parent, .nat n], body] :: ds =>
    if parent != prev then .error s!"log {who}: entry {k} does not name the entry before it"
    else if n != k then .error s!"log {who}: entry {k} is out of order"
    else
      match dataNote body with
      | none => .error s!"log {who}: entry {k} is not an entry"
      | some note =>
        readChainGo who (note :: acc) (Keep.entryName (.arr [.arr [.nat 0, parent, .nat n], body]))
          (k + 1) ds
  | k, _ :: _ => .error s!"log {who}: entry {k} has no link"

theorem readChainGo_eq (who : String) : ∀ (ds : List Data) (acc : List Note) (prev : Data) (k : Nat),
    readChainGo who acc prev k ds =
      (readChain who prev k ds).map fun r => (acc.reverse ++ r.1, r.2)
  | [], acc, prev, k => by simp [readChainGo, readChain, Except.map]
  | d :: ds, acc, prev, k => by
    by_cases h : ∃ parent n body, d = .arr [.arr [.nat 0, parent, .nat n], body]
    · obtain ⟨parent, n, body, rfl⟩ := h
      rw [readChainGo, readChain]
      split
      · rfl
      · split
        · rfl
        · cases dataNote body with
          | none => rfl
          | some note =>
            simp only [bind, Except.bind, pure, Except.pure]
            rw [readChainGo_eq who ds]
            cases readChain who _ (k + 1) ds <;> simp [Except.map]
    · have h' : ∀ parent n body, d = .arr [.arr [.nat 0, parent, .nat n], body] → False :=
        fun p n b e => h ⟨p, n, b, e⟩
      rw [readChainGo.eq_3 _ _ _ _ _ _ h', readChain.eq_3 _ _ _ _ _ h']; rfl

def readChainWalk (who : String) (prev : Data) (k : Nat) (ds : List Data) :
    Except String (List Note × Data) := readChainGo who [] prev k ds

@[csimp] theorem readChain_eq_walk : @readChain = @readChainWalk := by
  funext who prev k ds
  rw [readChainWalk, readChainGo_eq]
  cases readChain who prev k ds <;> simp [Except.map]

/-- The notes of a record, after its chain and its head are checked. -/
def recordNotes (who : String) (r : Record) : Except String (List Note) := do
  let c ← readChain who (.arr []) 0 r.entries
  match r.head with
  | some (n, name) =>
    if n != r.entries.length || name != c.2 then
      .error s!"log {who}: the head is not its last entry"
    else pure c.1
  | none => .error s!"log {who}: no head"

/-- Compare what a guest reported with the replay, place by place. -/
def compare (who : String) : Nat → List Nat → List String → List String → Except String Unit
  | _, [], [], [] => .ok ()
  | i, g :: gs, l :: ls, r :: rs =>
    if r == l then compare who (i + 1) gs ls rs
    else .error s!"process {g} ({who} {i}): reported {l}, replayed {r}"
  | _, gs, ls, _ =>
    .error s!"record {who} reports {ls.length} more processes and its log {gs.length} more"

/-- The crossings a guest acknowledged, and those it took, in its log's order. -/
def acksOf (ns : List Note) : List Nat := ns.filterMap fun | .ack k _ => some k | _ => none
def takingsOf (ns : List Note) : List Nat := ns.filterMap (·.taking)

def holdText (who : String) (hold : Nat) (es : List Charged) : Option (Nat × Nat) → String
  | some (k, m) => s!"full {who}: entry {k}, {m} cells counted\n"
  | none => s!"hold {who}: {hold} cells, {(es.filter (·.note.isCount)).length} counts\n"

structure Checked where
  text : String
  /-- The replay's lines of each side, for checks. -/
  linesA : List String
  linesB : List String

def checkedAll (program a b : ByteArray) (lines : Bool := true) : Except String Checked := do
  let ra ← readRecord "a" a
  let rb ← readRecord "b" b
  let na ← recordNotes "a" ra
  let nb ← recordNotes "b" rb
  if ra.me != rb.peer || rb.me != ra.peer then .error "the records do not name each other"
  if ra.budget != rb.budget then .error "the budgets differ"
  let steps := ra.budget.getD 0 0
  let cells := ra.budget.getD 1 0
  for (who, r) in [("a", ra), ("b", rb)] do
    if r.own.getD 0 0 < steps || r.own.getD 1 0 < cells then
      .error s!"record {who}: its budget is above its own limits"
  let holdA := ra.own.getD 2 0
  let holdB := rb.own.getD 2 0
  if defaultLimit < steps || turnSpace < cells || checkHold < holdA || checkHold < holdB then
    .error "the record asks more than this check runs"
  let t ← match Wire.readProgram program with
    | .error msg => .error ("bytes error: " ++ msg)
    | .ok t => pure t
  let (trace, m) ← match combineTrace na nb with
    | none => .error "the logs do not combine"
    | some r => pure r
  if acksOf nb != takingsOf na then .error "the acknowledgements of b are not the order a took them in"
  if acksOf na != takingsOf nb then .error "the acknowledgements of a are not the order b took them in"
  let begun := beginMade cells steps t
  let c₀ ← match begun.1 with
    | none => .error s!"no result within {steps} steps of a turn"
    | some c => pure c
  let places : Side → List Nat := fun | .a => m.placeA | .b => m.placeB
  let r := traceRun cells steps places c₀ 1 0 trace
  match r.stopped with
  | .refused (.answer _ _) => .error "an answer from outside in a crossing"
  | .refused ev => .error (renderData (eventData ev) ++ " cannot happen")
  | .unfinished ev => .error (s!"no result within {steps} steps of a turn, at " ++ renderData (eventData ev))
  | .ran => pure ()
  let ha ← match holdWalk holdA (beginCharge (reify t) begun.2) r.chargesA with
    | .error (k, why) => .error s!"hold a: entry {k}: {why}"
    | .ok x => pure x
  let hb ← match holdWalk holdB 0 r.chargesB with
    | .error (k, why) => .error s!"hold b: entry {k}: {why}"
    | .ok x => pure x
  let side (ps : List Nat) : List (Proc MValue MOutcome) := ps.filterMap (r.cfg.procs[·]?)
  let la := procLines (side m.placeA)
  let lb := procLines (side m.placeB)
  if lines then
    compare "a" 0 m.placeA ra.procs la
    compare "b" 0 m.placeB rb.procs lb
  pure ⟨"schedule: " ++ renderData (.arr (r.events.map eventData)) ++ "\n" ++
    "places a: " ++ renderData (.arr (m.placeA.map .nat)) ++ "\n" ++
    "places b: " ++ renderData (.arr (m.placeB.map .nat)) ++ "\n" ++
    s!"budget {steps} steps, {cells} cells\n" ++
    holdText "a" holdA r.chargesA ha ++ holdText "b" holdB r.chargesB hb ++
    renderProcs 0 r.cfg.procs, la, lb⟩

def checked (program a b : ByteArray) : Except String String :=
  (checkedAll program a b).map (·.text)

/-- Check two records against a program's bytes. `a` is the record of the
    guest that had the program. -/
def check (program a b : ByteArray) : String :=
  match checked program a b with
  | .ok text => "accepted\n" ++ text
  | .error msg => "refused: " ++ msg ++ "\n"

/-- Make a record's chain and head again from its entries' bodies, as a guest
    that lies would. For checks only. -/
def reseal (record : ByteArray) : String :=
  match readRecord "x" record with
  | .error msg => "error " ++ msg ++ "\n"
  | .ok r =>
    let bodies := r.entries.map fun
      | .arr [_, body] => body
      | d => d
    recordText r.me r.peer r.budget r.own bodies r.procs

/-- A lie made whole: guest `a`'s record (or `b`'s with `b`), made again and
    given the lines the replay of its log gives, so that the check cannot tell
    it from a run the guest made. For checks only. -/
def remake (program a b : ByteArray) (isA : Bool) : String :=
  let ra := (reseal a).toUTF8
  let rb := (reseal b).toUTF8
  match checkedAll program ra rb false with
  | .error msg => "error " ++ msg ++ "\n"
  | .ok c =>
    match readRecord "x" (if isA then ra else rb) with
    | .error msg => "error " ++ msg ++ "\n"
    | .ok r =>
      recordText r.me r.peer r.budget r.own (r.entries.map fun | .arr [_, body] => body | d => d)
        (if isA then c.linesA else c.linesB)

/-! Two guests in one process, for checks. -/

def roomLimit : Nat := 8000

/-- One exchange: the caller works and sends, the other takes, works and
    answers. -/
def exchange (ca cb : Guest → Nat) (ab : Guest × Guest) : Guest × Guest :=
  let a := ab.1.work ca workLimit
  let b := (ab.2.take (a.batch roomLimit)).work cb workLimit
  (a.take (b.batch roomLimit), b)

def pump (ca cb : Guest → Nat) : Nat → Guest × Guest → Guest × Guest
  | 0, ab => ab
  | n + 1, ab => if ab.1.closed then ab else pump ca cb n (exchange ca cb ab)

/-- How two guests in one process are set up. `A` is the guest given the
    program, `B` the caller. -/
structure Setup where
  frame : Nat := 100000
  limitA : Nat := defaultLimit
  limitB : Nat := defaultLimit
  turnA : Nat := defaultTurn
  turnB : Nat := defaultTurn
  holdA : Nat := defaultHold
  holdB : Nat := defaultHold
  countA : Guest → Nat := ledgerCount
  countB : Guest → Nat := ledgerCount
  far : Bool := false
  takeNew : Bool := false
  exchanges : Nat := 40

/-- Run a program on two guests until they close, or `exchanges` exchanges.
    The first of the pair is the caller, which has no process; the second is
    given the program. -/
def simulateWith (program : ByteArray) (s : Setup) : Guest × Guest :=
  pump s.countB s.countA s.exchanges
    (start false true false false s.limitB s.turnB s.holdB,
     (start true false s.far s.takeNew s.limitA s.turnA s.holdA).give program s.frame)

/-- The two records of `simulateWith`: the guest with the program first. -/
def simulatedWith (program : ByteArray) (s : Setup) : String × String :=
  let ba := simulateWith program s
  (ba.2.record "a" "b", ba.1.record "b" "a")

def simulated (program : ByteArray) (budget limit : Nat) (far takeNew : Bool) : String × String :=
  simulatedWith program { frame := budget, exchanges := limit, far, takeNew }

end Surface.Cross
