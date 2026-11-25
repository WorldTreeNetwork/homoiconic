import Reflect.Crossing

/-!
What a guest of a crossing holds, by a ledger.

A guest charges each entry of its log the cells it made: what its machine
runs made, as `runSpace`'s ledger counts them, the packets and programs it took
or made, and a fixed amount for the entry and for each new process. When an
entry passes what is left of its credit the guest counts the cells it holds
(the runtime does) and records the count, `held m` or `full m`.

Here: the measured runs (`runTurnMade`, `settleMade`, `turnMade`, `beginMade`,
`stepMade`), which give what `runTurnIn` and the channel runs give and the
cells they made beside it; the charges; the walk of one side's ledger that the
check runs (`holdWalk`); and the check's replay of a combined record in the
order the merge placed it, charging each entry as its guest did
(`traceRun`). `Reflect.HoldProof` says the measured runs are the runs, that
`traceRun` is `schedIn` on the schedule, and what `holdWalk` accepts.
-/
namespace Reflect

variable [Ops]

/-! The measured runs. -/

/-- `runSpace`, giving also the credit left where it ends. -/
def runSpaceLeft (sp : Space) : (fuel credit : Nat) → State → Ended × Nat
  | 0, credit, s => (.reached s, credit)
  | _ + 1, credit, .halted o => (.reached (.halted o), credit)
  | _ + 1, credit, .fault => (.reached .fault, credit)
  | fuel + 1, credit, .running c e stk frs =>
      if stepCost (.running c e stk frs) - 1 ≤ fuel then
        if atPrim (.running c e stk frs) then
          if answered (step (.running c e stk frs)) ≤ credit then
            runSpaceLeft sp (fuel - (stepCost (.running c e stk frs) - 1))
              (credit - answered (step (.running c e stk frs)))
              (step (.running c e stk frs))
          else if sp.count (.running c e stk frs) ≤ sp.bar ∧
              answered (step (.running c e stk frs)) ≤
                sp.cells - sp.count (.running c e stk frs) then
            runSpaceLeft sp (fuel - (stepCost (.running c e stk frs) - 1))
              (sp.cells - sp.count (.running c e stk frs) -
                answered (step (.running c e stk frs)))
              (step (.running c e stk frs))
          else (.full (.running c e stk frs), credit)
        else
          if owed (.running c e stk frs) ≤ credit then
            runSpaceLeft sp (fuel - (stepCost (.running c e stk frs) - 1))
              (credit - owed (.running c e stk frs))
              (step (.running c e stk frs))
          else if sp.count (.running c e stk frs) ≤ sp.bar ∧
              owed (.running c e stk frs) ≤ sp.cells - sp.count (.running c e stk frs) then
            runSpaceLeft sp (fuel - (stepCost (.running c e stk frs) - 1))
              (sp.cells - sp.count (.running c e stk frs) - owed (.running c e stk frs))
              (step (.running c e stk frs))
          else (.full (.running c e stk frs), credit)
      else (.reached (.running c e stk frs), credit)
termination_by fuel => fuel
decreasing_by all_goals omega

/-- `runTurnIn`, and the cells the turn made: its turn space less the credit
    it had left. With no count (`Space.ledger`) the credit is never given
    back, so this is every cell the run was charged. -/
def runTurnMade (cells budget : Nat) (s : State) : State × Nat :=
  let r := runSpaceLeft (.ledger cells) budget cells s
  ((match r.1 with
    | .full t => t
    | .reached (.halted (.value (.data d))) =>
        if d.writes (4 * cells) then .halted (.value (.data d)) else s
    | .reached t => t), cells - r.2)


def settleMade (cells budget : Nat) : MOutcome → Option (Status MValue MOutcome) × Nat
  | .value (.closure k e) =>
    let r := runTurnMade cells budget (.running (compile payloadTerm) [.closure k e] [] [])
    ((match r.1 with
      | .halted (.value (.data p)) => some (.waiting (.closure k e) p)
      | .halted (.value (.closure _ _)) => some (.finished .wrong)
      | .halted w => some (.finished w)
      | _ => none), r.2)
  | w => (some (.finished w), 0)

def turnMade (cells budget : Nat) (c : MValue) (a : Data) : Option (Status MValue MOutcome) × Nat :=
  let r := runTurnMade cells budget (.running (compile (resumeTerm a)) [c] [] [])
  match r.1 with
  | .halted w =>
    let s := settleMade cells budget w
    (s.1, r.2 + s.2)
  | _ => (none, r.2)

def beginMade (cells budget : Nat) (p : Term) : Option MConfig × Nat :=
  let r := runTurnMade cells budget (load (compile p))
  match r.1 with
  | .halted w =>
    let s := settleMade cells budget w
    (match s.1 with
     | some st => some ⟨[⟨st, []⟩], []⟩
     | none => none, r.2 + s.2)
  | _ => (none, r.2)

/-- `stepIn`, and the cells made by the runs of process `i`'s side of the event
    (its turn) and of the other side (the child's start, the receiver's
    turn), apart. -/
def stepMade (cells budget : Nat) (cfg : MConfig) : Event → Tried × Nat × Nat
  | .fresh i n =>
    match cfg.procs[i]? with
    | some ⟨.waiting c p, held⟩ =>
      match classify p with
      | .fresh =>
        if cfg.names.contains n then (.refused, 0, 0) else
        let r := turnMade cells budget c (.name n)
        ((match r.1 with
          | some st => .ok ⟨cfg.procs.set i ⟨st, n :: held⟩, n :: cfg.names⟩
          | none => .unfinished), r.2, 0)
      | _ => (.refused, 0, 0)
    | _ => (.refused, 0, 0)
  | .spawn i =>
    match cfg.procs[i]? with
    | some ⟨.waiting c p, held⟩ =>
      match classify p with
      | .spawn t arg =>
        let r := runTurnMade cells budget (load (compile (.app t (.lit arg))))
        match r.1 with
        | .halted w =>
          let ch := settleMade cells budget w
          let me := turnMade cells budget c (.arr [])
          ((match ch.1, me.1 with
            | some child, some st =>
              .ok ⟨cfg.procs.set i ⟨st, held⟩ ++ [⟨child, grant held arg⟩], cfg.names⟩
            | _, _ => .unfinished), me.2, r.2 + ch.2)
        | _ => (.unfinished, 0, r.2)
      | _ => (.refused, 0, 0)
    | _ => (.refused, 0, 0)
  | .comm i j =>
    match cfg.procs[i]?, cfg.procs[j]? with
    | some ⟨.waiting c p, held⟩, some ⟨.waiting c' p', held'⟩ =>
      match classify p, classify p' with
      | .send ch v, .receive ch' =>
        if ch == ch' && held.contains ch && held'.contains ch then
          let r := turnMade cells budget c (.arr [])
          let r' := turnMade cells budget c' v
          ((match r.1, r'.1 with
            | some st, some st' =>
              .ok ⟨(cfg.procs.set i ⟨st, held⟩).set j ⟨st', gain held' (grant held v)⟩, cfg.names⟩
            | _, _ => .unfinished), r.2, r'.2)
        else (.refused, 0, 0)
      | _, _ => (.refused, 0, 0)
    | _, _ => (.refused, 0, 0)
  | .answer i a =>
    match cfg.procs[i]? with
    | some ⟨.waiting c p, held⟩ =>
      match classify p with
      | .outside =>
        let r := turnMade cells budget c a
        ((match r.1 with
          | some st => .ok ⟨cfg.procs.set i ⟨st, held⟩, cfg.names⟩
          | none => .unfinished), r.2, 0)
      | _ => (.refused, 0, 0)
    | _ => (.refused, 0, 0)

/-! The charges. -/

/-- `acc` and the cells of the data waiting in `ds`, as `Data.cells` counts
    them, with the data still to count in a list (`homoiconic-q59.72`). -/
def cellsGo (acc : Nat) : List Data → Nat
  | [] => acc
  | .nat n :: ds => cellsGo (acc + natCells n) ds
  | .name n :: ds => cellsGo (acc + natCells n) ds
  | .text cs :: ds => cellsGo (acc + 1 + cs.length) ds
  | .arr xs :: ds => cellsGo (acc + 1 + xs.length) (xs ++ ds)
termination_by ds => Data.sizeList ds
decreasing_by all_goals simp_wf; all_goals (simp only [Data.sizeList, Data.size, Data.sizeList_append]; omega)

def cellsOf (d : Data) : Nat := cellsGo 0 [d]

/-- An entry of a log, its note and its place in the list. -/
def entryCells : Nat := 32
/-- A process: its place in the list and the names it holds. -/
def procCells : Nat := 128
/-- The term and the code made from a quoted program: at most two cells for
    each cell of its data form (`unreify` makes a term node for each array of
    the form, which has at least five cells, and `compile` a few instructions
    for each node). Read, not proved. -/
def codeCells (prog : Data) : Nat := 2 * cellsOf prog

/-- Crossings a guest may have put out and not had acknowledged. -/
def outLimit : Nat := 64
/-- Entries a side may record before it is full. -/
def entryLimit : Nat := 60000
/-- Processes a side may have before it is full. -/
def procLimit : Nat := 4096

/-- The packet that puts out process `held`'s request `p` as crossing `k`:
    a start `[0, k, program, start, names]` or a send
    `[1, k, name, message, names]`. -/
def packetOf (k : Nat) (held : List Nat) (p : Data) : Option Data :=
  match p, classify p with
  | .arr [.nat 3, prog, arg], .spawn _ _ =>
    some (.arr [.nat 0, .nat k, prog, arg, .arr ((grant held arg).map .nat)])
  | _, .send ch v => some (.arr [.nat 1, .nat k, .nat ch, v, .arr ((grant held v).map .nat)])
  | _, _ => none

def ackPacket (k : Nat) : Data := .arr [.nat 2, .nat k]

/-- A local event: the entry, the runs of both sides, and for a start the new
    process and its code. -/
def didCharge (cfg : MConfig) (ev : Event) (mine theirs : Nat) : Nat :=
  entryCells + mine + theirs +
    match ev with
    | .spawn i =>
      match cfg.procs[i]? with
      | some ⟨.waiting _ (.arr [.nat 3, prog, _]), _⟩ => procCells + codeCells prog
      | _ => 0
    | _ => 0

/-- A request put out: the entry, the asker's turn on `[]`, kept, and the
    packet. -/
def outCharge (turn : Nat) (pkt : Data) : Nat := entryCells + turn + cellsOf pkt

/-- A crossing taken: the entry, the runs on this side, the packet taken and
    the acknowledgement sent, and for a start the new process and its code. -/
def takeCharge (k : Nat) (pkt : Data) (made : Nat) : Nat :=
  entryCells + made + cellsOf pkt + cellsOf (ackPacket k) +
    match pkt with
    | .arr [.nat 0, _, prog, _, _] => procCells + codeCells prog
    | _ => 0

/-- Beginning the program: its runs, its process and its code. -/
def beginCharge (prog : Data) (made : Nat) : Nat := made + procCells + codeCells prog

/-! One side's ledger, as the check walks it. -/

/-- An entry of one side, with its charge and how many processes the side has
    after it. -/
structure Charged where
  note : Note
  cost : Nat
  procs : Nat

def Note.isCount : Note → Bool
  | .held _ => true
  | .full _ => true
  | _ => false

def Note.isAck : Note → Bool
  | .ack _ _ => true
  | _ => false

/-- The most a count may be for the guest to go on: three quarters of its
    hold, as `Space.bar`. -/
def holdBar (hold : Nat) : Nat := hold - hold / 4

/-- What is left after `full`: acknowledgements only, at most `outLimit`. -/
def afterFull (k : Nat) (rest : List Charged) : Except (Nat × String) Unit :=
  match rest.findIdx? (fun e => !e.note.isAck) with
  | some i => .error (k + i, "an entry after full")
  | none => if rest.length ≤ outLimit then .ok () else .error (k + outLimit, "an entry after full")

/-- Walk one side's entries with their charges. `k` is the place of the next
    entry, `credit` what is left, `must` that the last entry spent the credit
    or reached a cap so that a count comes now, `cap` that it reached a cap.
    Gives where the side was full and its count, or none, or the first entry
    that is wrong and why. -/
def holdGo (hold : Nat) : (k credit : Nat) → (must cap : Bool) → List Charged →
    Except (Nat × String) (Option (Nat × Nat))
  | k, _, must, _, [] =>
    if must then .error (k, "the ledger was spent and not counted") else .ok none
  | k, credit, must, cap, e :: rest =>
    match e.note with
    | .held m =>
      if !must then .error (k, "a count where the ledger was not spent")
      else if cap then .error (k, "a cap reached and not full")
      else if holdBar hold < m then .error (k, "a count past the bar that is not full")
      else holdGo hold (k + 1) (hold - m) false false rest
    | .full m =>
      if !must then .error (k, "a count where the ledger was not spent")
      else if !cap && m ≤ holdBar hold then .error (k, "full within the bar")
      else (afterFull (k + 1) rest).map fun _ => some (k, m)
    | _ =>
      if must then .error (k, "the ledger was spent and not counted")
      else if e.cost ≤ credit && !(entryLimit ≤ k + 1 || procLimit ≤ e.procs) then
        holdGo hold (k + 1) (credit - e.cost) false false rest
      else holdGo hold (k + 1) credit true (entryLimit ≤ k + 1 || procLimit ≤ e.procs) rest

/-- The ledger of a side with hold `hold`, whose begin was charged `first`. -/
def holdWalk (hold first : Nat) (es : List Charged) : Except (Nat × String) (Option (Nat × Nat)) :=
  if first ≤ hold then holdGo hold 0 (hold - first) false false es
  else holdGo hold 0 0 true false es

/-! The check's replay, in the order the merge placed the entries. -/

/-- How the replay ended, the configuration, and each side's entries with
    their charges, in each side's log order. -/
structure Replayed where
  events : List Event
  cfg : MConfig
  stopped : Stopped
  chargesA : List Charged
  chargesB : List Charged


/-- Run events in order with the measured runs; the cells of the first side
    of each and of the other, summed. -/
def runEvents (cells budget : Nat) : MConfig → List Event → List Event × MConfig × Stopped × Nat × Nat
  | cfg, [] => ([], cfg, .ran, 0, 0)
  | cfg, ev :: evs =>
    let r := stepMade cells budget cfg ev
    match r.1 with
    | .ok mid =>
      let q := runEvents cells budget mid evs
      (ev :: q.1, q.2.1, q.2.2.1, r.2.1 + q.2.2.2.1, r.2.2 + q.2.2.2.2)
    | .refused => ([], cfg, .refused ev, r.2.1, r.2.2)
    | .unfinished => ([], cfg, .unfinished ev, r.2.1, r.2.2)

/-- The packet of the crossing an event of a taking stands for: from the
    asker's request in `cfg`, before the event. -/
def takenPacket (cfg : MConfig) (k : Nat) : List Event → Data
  | .spawn g :: _ | .comm g _ :: _ =>
    match cfg.procs[g]? with
    | some ⟨.waiting _ p, held⟩ => (packetOf k held p).getD (.arr [])
    | _ => .arr []
  | _ => .arr []

/-- The charge of an entry whose events ran, as its guest charged it, and how
    many processes it added to its side. `mine` and `theirs` are what the
    events' two sides made; `cfg` is the configuration before them. -/
def entryCost (cells budget : Nat) (places : List Nat) (cfg : MConfig) (n : Note)
    (evs : List Event) (mine theirs : Nat) : Nat × Nat :=
  match n with
  | .did ev =>
    let more := match ev with | .spawn _ => 1 | _ => 0
    match evs with
    | [gev] => (didCharge cfg gev mine theirs, more)
    | _ => (entryCells + mine + theirs, more)
  | .out i k =>
    match places[i]? with
    | some g =>
      match cfg.procs[g]? with
      | some ⟨.waiting c p, held⟩ =>
        (outCharge (turnMade cells budget c (.arr [])).2 ((packetOf k held p).getD (.arr [])), 0)
      | _ => (entryCells, 0)
    | none => (entryCells, 0)
  | .spawnIn k => (takeCharge k (takenPacket cfg k evs) theirs, 1)
  | .sendIn k _ => (takeCharge k (takenPacket cfg k evs) theirs, 0)
  | .ack _ _ => (entryCells, 0)
  | .held _ => (0, 0)
  | .full _ => (0, 0)

def isAnswer : Event → Bool
  | .answer _ _ => true
  | _ => false

/-- Replay a trace from `cfg`. `places` are the global places of each side's
    local places, from the end of the walk; `procsA`, `procsB` how many
    processes each side has so far. An answer from outside has no place in
    a crossing and stops the replay as refused. -/
def traceRun (cells budget : Nat) (places : Side → List Nat) :
    MConfig → (procsA procsB : Nat) → List (Side × Note × List Event) → Replayed
  | cfg, _, _, [] => ⟨[], cfg, .ran, [], []⟩
  | cfg, pa, pb, (s, n, evs) :: rest =>
    match evs.find? isAnswer with
    | some ev => ⟨[], cfg, .refused ev, [], []⟩
    | none =>
      let q := runEvents cells budget cfg evs
      match q.2.2.1 with
      | .ran =>
        let c := entryCost cells budget (places s) cfg n evs q.2.2.2.1 q.2.2.2.2
        match s with
        | .a =>
          let r := traceRun cells budget places q.2.1 (pa + c.2) pb rest
          { r with events := q.1 ++ r.events, chargesA := ⟨n, c.1, pa + c.2⟩ :: r.chargesA }
        | .b =>
          let r := traceRun cells budget places q.2.1 pa (pb + c.2) rest
          { r with events := q.1 ++ r.events, chargesB := ⟨n, c.1, pb + c.2⟩ :: r.chargesB }
      | stop => ⟨q.1, q.2.1, stop, [], []⟩

end Reflect
