import Surface.Chan
import Surface.Keep
import Reflect.Crossing
import Wire.Form

/-!
A guest of a run on two machines, and the check of what two guests recorded.

A guest holds its own processes and runs them with the one-machine functions
(`stepRun`, `turnRun`, `settleRun`), each machine run with the guest's budget.
A start or a send whose other process is on the peer is a *crossing*: it is put
out as a packet, taken in on the other guest, and acknowledged. Each thing a
guest does is a `Reflect.Note` in its log.

`check` reads two records, combines the logs (`Reflect.combine`), replays the
schedule on one machine (`schedRun`), and compares each process with the line
its guest reported.

What a guest does is tested, not proved. Of the check it is proved that an
accepted record is a run of the one-machine network (`accepted_network`).
-/
namespace Surface.Cross
open Reflect

def noteData : Note → Data
  | .did ev => .arr [.nat 0, eventData ev]
  | .out i k => .arr [.nat 1, .nat i, .nat k]
  | .spawnIn k => .arr [.nat 2, .nat k]
  | .sendIn k j => .arr [.nat 3, .nat k, .nat j]
  | .ack k i => .arr [.nat 4, .nat k, .nat i]

def dataNote : Data → Option Note
  | .arr [.nat 0, d] => (dataEvent d).map .did
  | .arr [.nat 1, .nat i, .nat k] => some (.out i k)
  | .arr [.nat 2, .nat k] => some (.spawnIn k)
  | .arr [.nat 3, .nat k, .nat j] => some (.sendIn k j)
  | .arr [.nat 4, .nat k, .nat i] => some (.ack k i)
  | _ => none

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
  /-- The budget of each machine run. The guest with the program is given it;
      the other takes it from the first batch that carries one. 0: not known. -/
  budget : Nat := 0
  /-- Side `a` before it is given its program. -/
  waiting : Bool := false
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
  /-- Every packet sent, in order; its place is its number. -/
  sent : Array Data := #[]
  /-- How many of `sent` the peer has counted. -/
  counted : Nat := 0
  /-- How many of the peer's packets were accepted. -/
  got : Nat := 0
  /-- `work` found nothing possible. -/
  resting : Bool := false
  /-- The peer's last batch said it was idle and carried no packet. -/
  peerQuiet : Bool := false
  closed : Bool := false
  error : String := ""

/-- The most bytes one crossing's packet may have. -/
def packetLimit : Nat := 6000

def Guest.note (g : Guest) (n : Note) : Guest := { g with log := n :: g.log }

def Guest.post (g : Guest) (pkt : Data) : Guest := { g with sent := g.sent.push pkt }

/-- The process waits to send on a name it holds. -/
def wantsSend (q : Proc MValue MOutcome) : Bool :=
  match q.status with
  | .waiting _ p =>
    match classify p with
    | .send ch _ => q.held.contains ch
    | _ => false
  | _ => false

/-- The configuration with every held or stuck process hidden, so that the
    scheduler neither chooses it nor finds it as a partner. -/
def Guest.masked (g : Guest) : MConfig :=
  ⟨g.cfg.procs.mapIdx fun i q =>
      if g.asked.any (·.place == i) || g.stuck.contains i then ⟨.finished .wrong, []⟩ else q,
    g.cfg.names⟩

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

/-- Work one packet from the peer. -/
def Guest.takeIn (g : Guest) : Option Guest :=
  match g.inbox with
  | [] => none
  | pkt :: rest =>
    let g : Guest := { g with inbox := rest }
    match pkt with
    | .arr [.nat 0, .nat k, prog, start, .arr held] =>
      match unreify prog, numbers held with
      | some t, some hs =>
        match runTurn g.budget (load (compile (.app t (.lit start)))) with
        | .halted w =>
          match settleRun g.budget w with
          | some child =>
            let cfg : MConfig := ⟨g.cfg.procs ++ [⟨child, hs⟩], g.cfg.names⟩
            some ((({ g with cfg }).note (.spawnIn k)).post (.arr [.nat 2, .nat k]))
          | none => some g
        | _ => some g
      | _, _ => some g
    | .arr [.nat 1, .nat k, .nat name, message, .arr held] =>
      match numbers held with
      | some hs => some { g with pending := g.pending ++ [⟨k, name, message, hs⟩] }
      | none => some g
    | .arr [.nat 2, .nat k] =>
      match g.asked.find? (·.k == k) with
      | some a =>
        match g.cfg.procs[a.place]? with
        | some q =>
          let cfg : MConfig := ⟨g.cfg.procs.set a.place ⟨a.next, q.held⟩, g.cfg.names⟩
          some (({ g with cfg, asked := g.asked.filter (·.k != k) }).note (.ack k a.place))
        | none => some g
      | none => some g
    | _ => some g

/-- Take one of the peer's pending sends that a local receiver can take: the
    oldest, or the newest with `takeNew`. -/
def Guest.takeSend (g : Guest) : Option Guest :=
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
        match turnRun g.budget c p.message with
        | some st =>
          let cfg : MConfig := ⟨g.cfg.procs.set j ⟨st, gain held p.held⟩, g.cfg.names⟩
          some ((({ g with cfg }).note (.sendIn p.k j)).post (.arr [.nat 2, .nat p.k]))
        | none => some g
      | _ => some g
    | none => some g

/-- Put process `i`'s start or send out to the peer. Its turn on `[]` is run
    first and kept; when that does not finish nothing leaves. -/
def Guest.ask (g : Guest) (i : Nat) : Option Guest :=
  match g.cfg.procs[i]? with
  | some ⟨.waiting c p, held⟩ =>
    let pkt : Option Data :=
      match p, classify p with
      | .arr [.nat 3, prog, arg], .spawn _ _ =>
        some (.arr [.nat 0, .nat g.outs, prog, arg, .arr ((grant held arg).map .nat)])
      | _, .send ch v =>
        some (.arr [.nat 1, .nat g.outs, .nat ch, v, .arr ((grant held v).map .nat)])
      | _, _ => none
    match pkt with
    | some pkt =>
      if (Wire.write pkt).size > packetLimit then some { g with stuck := i :: g.stuck } else
      match turnRun g.budget c (.arr []) with
      | some next =>
        some ((({ g with asked := ⟨i, g.outs, next⟩ :: g.asked, outs := g.outs + 1 }).note
          (.out i g.outs)).post pkt)
      | none => some { g with stuck := i :: g.stuck }
    | none => none
  | _ => none

/-- A local event `ev` of process `i`, run as one machine runs it. -/
def Guest.happen (g : Guest) (i : Nat) (ev : Event) : Guest :=
  match stepRun g.budget g.cfg ev with
  | .ok cfg => ({ g with cfg }).note (.did ev)
  | _ => { g with stuck := i :: g.stuck }

/-- One local event, or one request put out. A new channel is named by the
    guest's side, even on `a` and odd on `b`, not by `pick`. -/
def Guest.act (g : Guest) : Option Guest :=
  let m := g.masked
  match pick m with
  | some (.fresh i _) =>
    let n := 2 * g.made + (if g.side = .a then 0 else 1)
    some ({ g with made := g.made + 1 }.happen i (.fresh i n))
  | some (.spawn i) => if g.far then g.ask i else some (g.happen i (.spawn i))
  | some (.comm i j) => some (g.happen i (.comm i j))
  | some (.answer _ _) => none
  | none =>
    match findProc wantsSend m.procs with
    | some i => g.ask i
    | none => none

def Guest.step (g : Guest) : Option Guest :=
  match g.takeIn with
  | some g => some g
  | none =>
    match g.takeSend with
    | some g => some g
    | none => g.act

/-- Work until nothing is possible, or `limit` steps. -/
def Guest.work : Nat → Guest → Guest
  | 0, g => g
  | limit + 1, g =>
    match g.step with
    | some g' => Guest.work limit g'
    | none => { g with resting := true }

def workLimit : Nat := 256

/-- Nothing to do and nothing the peer has not counted. A guest that still
    waits for its program is not idle. -/
def Guest.idle (g : Guest) : Bool :=
  !g.waiting && g.resting && g.inbox.isEmpty && g.counted == g.sent.size

/-- The guest that opens the exchanges closes when it is idle and the peer's
    last batch was quiet. The other closes when told. -/
def Guest.closing (g : Guest) : Bool :=
  g.closed || (g.caller && g.idle && g.peerQuiet)

/-- The batch for the peer: a flag, how many of its packets were accepted, the
    budget, and the packets it has not counted, as many as fit in `room` bytes. -/
def Guest.batch (g : Guest) (room : Nat) : ByteArray :=
  let flag := if g.closing then 2 else if g.idle then 1 else 0
  let pkts := (List.range (g.sent.size - g.counted)).foldl (fun (acc : List Data × Nat × Bool) d =>
    let seq := g.counted + d
    match g.sent[seq]? with
    | some pkt =>
      let size := (Wire.write pkt).size + 16
      if acc.2.2 || acc.2.1 + size > room then (acc.1, acc.2.1, true)
      else (acc.1 ++ [.arr [.nat seq, pkt]], acc.2.1 + size, false)
    | none => acc) ([], 64, false)
  Wire.write (.arr [.nat flag, .nat g.got, .nat g.budget, .arr pkts.1])

/-- Take a batch from the peer. Packets are only queued here. -/
def Guest.take (g : Guest) (bytes : ByteArray) : Guest :=
  match Wire.read bytes with
  | .ok (.arr [.nat flag, .nat got, .nat budget, .arr pkts]) =>
    let g := { g with counted := max g.counted (min got g.sent.size),
                      peerQuiet := flag ≥ 1 && pkts.isEmpty,
                      budget := if g.budget == 0 then budget else g.budget }
    let g := pkts.foldl (fun (g : Guest) p =>
      match p with
      | .arr [.nat seq, pkt] =>
        if seq == g.got then { g with inbox := g.inbox ++ [pkt], got := g.got + 1, resting := false }
        else g
      | _ => g) g
    if flag == 2 then { g with closed := true } else g
  | _ => g

/-- Begin a guest with no process. The guest that will be given the program
    is side `a`, and waits for it. -/
def start (hasProgram caller far takeNew : Bool) : Guest :=
  { side := if hasProgram then .a else .b, caller, far, takeNew, waiting := hasProgram }

/-- Give the waiting guest its program, in its byte form, and the budget of
    each machine run. The program is begun as the first process. -/
def Guest.give (g : Guest) (program : ByteArray) (budget : Nat) : Guest :=
  if !g.waiting then g else
  match Wire.readProgram program with
  | .error msg => { g with error := "bytes error: " ++ msg }
  | .ok t =>
    match beginRun budget t with
    | some cfg => { g with cfg, budget, waiting := false, resting := false }
    | none => { g with error := s!"no result within {budget} steps of a turn" }

/-- 0: there is work. 1: resting. 2: closed. 3: failed. -/
def Guest.state (g : Guest) : UInt8 :=
  if g.error != "" then 3 else if g.closed then 2
  else if g.waiting || (g.resting && g.inbox.isEmpty) then 1 else 0

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

def procLine (q : Proc MValue MOutcome) : String :=
  (match q.status with
   | .waiting _ p => "waiting on " ++ renderData p
   | .finished w => renderMOutcome w) ++
    "; holds " ++ renderData (.arr (q.held.map .name))

def recordText (me peer : String) (budget : Nat) (bodies : List Data) (procs : List String) :
    String :=
  let s := chain (.arr []) 0 bodies
  s!"me {me}\npeer {peer}\nbudget {budget}\n" ++
    String.join (s.1.map fun e => "entry " ++ renderData e ++ "\n") ++
    s!"head {s.1.length} " ++ renderData s.2 ++ "\n" ++
    String.join (procs.map fun l => "proc " ++ l ++ "\n")

/-- What a guest hands over: its name, its peer's, the budget, its log, the
    head, and a line for each of its processes. -/
def Guest.record (g : Guest) (me peer : String) : String :=
  if g.error != "" then "error " ++ g.error ++ "\n" else
  recordText me peer g.budget (g.log.reverse.map noteData) (g.cfg.procs.map procLine)

structure Record where
  me : String := ""
  peer : String := ""
  budget : Option Nat := none
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

def readLines (who : String) : Nat → List String → Record → Except String Record
  | _, [], r => .ok r
  | k, l :: ls, r =>
    if l == "" then readLines who (k + 1) ls r
    else if l.startsWith "me " then readLines who (k + 1) ls { r with me := (l.drop 3).toString }
    else if l.startsWith "peer " then readLines who (k + 1) ls { r with peer := (l.drop 5).toString }
    else if l.startsWith "budget " then
      match (l.drop 7).toString.toNat? with
      | some n => readLines who (k + 1) ls { r with budget := some n }
      | none => .error s!"record {who}: line {k} is not read"
    else if l.startsWith "entry " then
      match readData (l.drop 6).toString with
      | some d => readLines who (k + 1) ls { r with entries := r.entries ++ [d] }
      | none => .error s!"record {who}: line {k} is not read"
    else if l.startsWith "head " then
      match ((l.drop 5).toString.splitOn " ") with
      | [n, name] =>
        match n.toNat?, readData name with
        | some n, some d => readLines who (k + 1) ls { r with head := some (n, d) }
        | _, _ => .error s!"record {who}: line {k} is not read"
      | _ => .error s!"record {who}: line {k} is not read"
    else if l.startsWith "proc " then
      readLines who (k + 1) ls { r with procs := r.procs ++ [(l.drop 5).toString] }
    else .error s!"record {who}: line {k} is not read"

def readRecord (who : String) (bytes : ByteArray) : Except String Record :=
  match String.fromUTF8? bytes with
  | none => .error s!"record {who}: not text"
  | some s => readLines who 0 (s.splitOn "\n") {}

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
def compare (who : String) (cfg : MConfig) : Nat → List Nat → List String → Except String Unit
  | _, [], [] => .ok ()
  | i, g :: gs, l :: ls =>
    match cfg.procs[g]? with
    | some q =>
      if procLine q == l then compare who cfg (i + 1) gs ls
      else .error s!"process {g} ({who} {i}): reported {l}, replayed {procLine q}"
    | none => .error s!"process {g} ({who} {i}): not in the replay"
  | _, gs, ls =>
    .error s!"record {who} reports {ls.length} more processes and its log {gs.length} more"

def checked (program a b : ByteArray) : Except String String := do
  let ra ← readRecord "a" a
  let rb ← readRecord "b" b
  let na ← recordNotes "a" ra
  let nb ← recordNotes "b" rb
  if ra.me != rb.peer || rb.me != ra.peer then .error "the records do not name each other"
  match ra.budget, rb.budget with
  | some budget, some budget' =>
    if budget != budget' then .error "the budgets differ"
    match Wire.readProgram program with
    | .error msg => .error ("bytes error: " ++ msg)
    | .ok t =>
      match combineMix na nb with
      | none => .error "the logs do not combine"
      | some (evs, m) =>
        match beginRun budget t with
        | none => .error s!"no result within {budget} steps of a turn"
        | some c₀ =>
          match schedRun budget c₀ evs with
          | (_, cfg, .ran) =>
            compare "a" cfg 0 m.placeA ra.procs
            compare "b" cfg 0 m.placeB rb.procs
            pure ("schedule: " ++ renderData (.arr (evs.map eventData)) ++ "\n" ++
              "places a: " ++ renderData (.arr (m.placeA.map .nat)) ++ "\n" ++
              "places b: " ++ renderData (.arr (m.placeB.map .nat)) ++ "\n" ++
              renderProcs 0 cfg.procs)
          | (_, _, .refused ev) => .error (renderData (eventData ev) ++ " cannot happen")
          | (_, _, .unfinished ev) =>
            .error (s!"no result within {budget} steps of a turn, at " ++ renderData (eventData ev))
  | _, _ => .error "a record has no budget"

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
    recordText r.me r.peer (r.budget.getD 0) bodies r.procs

/-! Two guests in one process, for checks. -/

def roomLimit : Nat := 8000

/-- One exchange: the caller works and sends, the other takes, works and
    answers. -/
def exchange (ab : Guest × Guest) : Guest × Guest :=
  let a := ab.1.work workLimit
  let b := (ab.2.take (a.batch roomLimit)).work workLimit
  (a.take (b.batch roomLimit), b)

def pump : Nat → Guest × Guest → Guest × Guest
  | 0, ab => ab
  | n + 1, ab => if ab.1.closed then ab else pump n (exchange ab)

/-- Run a program on two guests until they close, or `limit` exchanges. The
    first of the pair is the caller, which has no process; the second is given
    the program. -/
def simulate (program : ByteArray) (budget limit : Nat) (far takeNew : Bool) : Guest × Guest :=
  pump limit (start false true false false, (start true false far takeNew).give program budget)

/-- The two records of `simulate`: the guest with the program first. -/
def simulated (program : ByteArray) (budget limit : Nat) (far takeNew : Bool) : String × String :=
  let ba := simulate program budget limit far takeNew
  (ba.2.record "a" "b", ba.1.record "b" "a")

end Surface.Cross
