import Surface.Cross

/-!
Two guests that follow the protocol, as a transition system.

A guest *follows the protocol* when its state changes only by the functions of
`Surface.Cross` that the image calls: `Guest.step` (one step of `Guest.work`),
the rest `Guest.work` takes when no step is possible, `Guest.give`, and
`Guest.take` of a batch its peer made with `Guest.batch`. `Pair` is two such
guests and every batch either has made; `Move` is one change; `Reach` is what
can be reached from two guests just started.

What the model assumes, and nothing else:

* **The bytes.** A batch is taken as the data it was made from
  (`Guest.takeData` of a `Guest.batchData`). `Guest.take` reads bytes with
  `Wire.read` and `Guest.batch` writes them with `Wire.write`
  (`Guest.take_eq`, `Guest.batch_eq`); that `Wire.read (Wire.write d)` gives
  `d` back is tested (P4), not proved, so it is a hypothesis wherever bytes
  are spoken of (`Reach.exchange`).
* **The transport.** A batch a guest takes is one its peer made, at some
  earlier time, with some room. Nothing else is assumed of delivery: a batch
  may be lost, taken twice, or taken after a later one. So no order is assumed
  between batches, and none within the two directions. The theorems of
  `Surface.CrossProof` hold of every state so reached.
* **The count.** Each step is given some count of the cells held, any function
  of the guest; the image's is `reflect_live_cells`.
* **The program.** `prog` is the program side `a` was given, kept beside the
  guests because `Guest.begin` forgets it.

What the guest code assumes of the transport and the model does not: the guest
that opens the exchanges closes when it is idle and the last batch it *took*
said the peer was idle and carried no packet (`Guest.closing`). That is a
sound reason to stop only if that batch was made after the peer had every
packet of this guest's, which holds when batches are answered and taken one
exchange at a time (one QUIC connection each, a stream read whole and in
order, as `unikernel/net.zig` does it). The model has no such rule and its
theorems do not need one: they speak of states where nothing is in flight
(`Pair.Quiet`), however the guests came to stop there.
-/
namespace Surface.Cross
open Reflect

/-- `Guest.take`, of the batch as data. -/
def Guest.takeData (g : Guest) : Data → Guest
  | .arr [.nat flag, .nat got, .nat steps, .nat cells, .arr pkts] =>
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

/-- Taking bytes is taking the data they read as, or nothing. -/
theorem Guest.take_eq (g : Guest) (bytes : ByteArray) :
    g.take bytes = match Wire.read bytes with
      | .ok d => g.takeData d
      | .error _ => g := by
  unfold Guest.take
  cases h : Wire.read bytes with
  | error e => rfl
  | ok d =>
    show _ = g.takeData d
    by_cases hs : ∃ flag got steps cells pkts,
        d = .arr [.nat flag, .nat got, .nat steps, .nat cells, .arr pkts]
    · obtain ⟨flag, got, steps, cells, pkts, rfl⟩ := hs
      rfl
    · have hr : g.takeData d = g := by
        unfold Guest.takeData
        split
        · exact absurd ⟨_, _, _, _, _, rfl⟩ hs
        · rfl
      rw [hr]
      split
      · next heq => cases heq; exact absurd ⟨_, _, _, _, _, rfl⟩ hs
      · rfl

/-- `Guest.batch`, as data. -/
def Guest.batchData (g : Guest) (room : Nat) : Data :=
  let flag := if g.closing then 2 else if g.idle then 1 else 0
  let pkts := g.sent.foldl (fun (acc : List Data × Nat × Bool × Nat) pkt =>
    let size := (Wire.write pkt).size + 16
    if acc.2.2.1 || acc.2.1 + size > room then (acc.1, acc.2.1, true, acc.2.2.2 + 1)
    else (acc.1 ++ [.arr [.nat acc.2.2.2, pkt]], acc.2.1 + size, false, acc.2.2.2 + 1))
    ([], 64, false, g.sentBase)
  .arr [.nat flag, .nat g.got, .nat g.budget, .nat g.cells, .arr pkts.1]

theorem Guest.batch_eq (g : Guest) (room : Nat) : g.batch room = Wire.write (g.batchData room) := rfl

/-- Two guests, every batch either has made, and the program `a` was given. -/
structure Pair where
  /-- The guest that is given the program. -/
  a : Guest
  b : Guest
  /-- Every batch `b` has made, as data. -/
  toA : List Data
  /-- Every batch `a` has made, as data. -/
  toB : List Data
  /-- The program `a` took, when it took one. -/
  prog : Option Term

/-- How a guest is set up when it starts. -/
structure Knobs where
  caller : Bool
  far : Bool
  takeNew : Bool
  limit : Nat
  turn : Nat
  hold : Nat

/-- Two guests just started. -/
def Pair.first (ka kb : Knobs) : Pair :=
  { a := start true ka.caller ka.far ka.takeNew ka.limit ka.turn ka.hold,
    b := start false kb.caller kb.far kb.takeNew kb.limit kb.turn kb.hold,
    toA := [], toB := [], prog := none }

/-- The program a `give` leaves with the pair: the one read, when the guest
    takes it. -/
def handed (g : Guest) (bytes : ByteArray) (old : Option Term) : Option Term :=
  if !g.waiting || g.program.isSome then old else
  match Wire.readProgram bytes with
  | .ok t => some t
  | .error _ => old

/-- One change of the pair. -/
inductive Move : Pair → Pair → Prop where
  /-- One step of `a`'s `work`, with some count. -/
  | stepA {s : Pair} (cnt : Guest → Nat) {g : Guest} (h : s.a.step cnt = some g) :
      Move s { s with a := g }
  /-- `a`'s `work` finds nothing possible and rests. -/
  | restA {s : Pair} (cnt : Guest → Nat) (h : s.a.step cnt = none) :
      Move s { s with a := { s.a with resting := true } }
  /-- `a` is handed a program's bytes and a budget. -/
  | giveA {s : Pair} (bytes : ByteArray) (budget : Nat) :
      Move s { s with a := s.a.give bytes budget, prog := handed s.a bytes s.prog }
  /-- `a` makes a batch. -/
  | sendA {s : Pair} (room : Nat) : Move s { s with toB := s.a.batchData room :: s.toB }
  /-- `a` takes a batch `b` made. -/
  | takeA {s : Pair} {d : Data} (h : d ∈ s.toA) : Move s { s with a := s.a.takeData d }
  | stepB {s : Pair} (cnt : Guest → Nat) {g : Guest} (h : s.b.step cnt = some g) :
      Move s { s with b := g }
  | restB {s : Pair} (cnt : Guest → Nat) (h : s.b.step cnt = none) :
      Move s { s with b := { s.b with resting := true } }
  | giveB {s : Pair} (bytes : ByteArray) (budget : Nat) :
      Move s { s with b := s.b.give bytes budget }
  | sendB {s : Pair} (room : Nat) : Move s { s with toA := s.b.batchData room :: s.toA }
  | takeB {s : Pair} {d : Data} (h : d ∈ s.toB) : Move s { s with b := s.b.takeData d }

/-- What two guests that follow the protocol can reach. -/
inductive Reach : Pair → Prop where
  | first (ka kb : Knobs) : Reach (Pair.first ka kb)
  | move {s s' : Pair} (h : Reach s) (m : Move s s') : Reach s'

/-- Nothing is in flight: neither guest keeps a packet the other has not
    counted, and neither has an accepted packet it has not worked. -/
def Pair.Quiet (s : Pair) : Prop :=
  s.a.sent = [] ∧ s.b.sent = [] ∧ s.a.inbox = [] ∧ s.b.inbox = []

end Surface.Cross
