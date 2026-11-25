import Reflect.Channel

/-!
A run on two guests, as one schedule.

One program runs as processes spread over two guests, `a` and `b`. Guest `a`
starts the program as its first process and `b` starts with none. Each guest
keeps a log of what it did: its local events, with its own places, and its
halves of the *crossings*, the starts and meetings whose two processes are on
different guests.

A crossing goes `out` on the guest of the process that asked, is taken in on
the other (`spawnIn`, `sendIn`), and is acknowledged on the first (`ack`). The
process that asked is held from `out` to `ack`.

`combine` walks two logs and gives one schedule of the one-machine network
(`Reflect.Network`), with global places, or nothing. The event of a crossing
sits where the crossing was taken. `accept` runs that schedule with `schedRun`.
Nothing here says what a guest does; the definitions say what two logs mean
together, and whether they mean anything.
-/
namespace Reflect

inductive Side where
  | a
  | b
  deriving DecidableEq, Repr

def Side.other : Side → Side
  | .a => .b
  | .b => .a

/-- One entry of a guest's log. Places are the guest's own; `k` counts the
    crossings of the guest that put them out, from 0. -/
inductive Note where
  /-- A local event happened. -/
  | did (ev : Event)
  /-- Process `i`'s start or send was put out to the peer as crossing `k`. -/
  | out (i k : Nat)
  /-- The peer's crossing `k`, a start, was taken: the child is the next
      process here. -/
  | spawnIn (k : Nat)
  /-- The peer's crossing `k`, a send, was taken by local receiver `j`. -/
  | sendIn (k j : Nat)
  /-- The peer took crossing `k`, and process `i` continued. -/
  | ack (k i : Nat)
  /-- The guest's ledger was spent; it counted `m` cells held and went on. -/
  | held (m : Nat)
  /-- The guest counted `m` cells held, or reached a cap, and stopped. -/
  | full (m : Nat)
  deriving Repr, BEq

inductive Crossed where
  | offered
  | taken
  | acked
  deriving DecidableEq, Repr

/-- A crossing: the global place of the process that asked, and how far it
    has got. -/
structure Crossing where
  asker : Nat
  state : Crossed

/-- The state of the walk: the global place of each local place of each guest,
    the number of processes so far, and each guest's crossings so far. -/
structure Mix where
  placeA : List Nat
  placeB : List Nat
  total : Nat
  outA : List Crossing
  outB : List Crossing

/-- Guest `a` has the program as its place 0; `b` has no process. -/
def Mix.first : Mix := ⟨[0], [], 1, [], []⟩

def Mix.places (m : Mix) : Side → List Nat
  | .a => m.placeA
  | .b => m.placeB

def Mix.outs (m : Mix) : Side → List Crossing
  | .a => m.outA
  | .b => m.outB

def Mix.setOuts (m : Mix) : Side → List Crossing → Mix
  | .a, cs => { m with outA := cs }
  | .b, cs => { m with outB := cs }

/-- Guest `s` gains a process: its next local place is the next global place. -/
def Mix.grow (m : Mix) : Side → Mix
  | .a => { m with placeA := m.placeA ++ [m.total], total := m.total + 1 }
  | .b => { m with placeB := m.placeB ++ [m.total], total := m.total + 1 }

/-- The process at global place `g` asked for a crossing not yet acknowledged. -/
def Mix.held (m : Mix) (g : Nat) : Bool :=
  (m.outA ++ m.outB).any (fun c => c.asker == g && decide (c.state ≠ .acked))

/-- The global place of local place `i` of guest `s`, when it is not held. -/
def Mix.free (m : Mix) (s : Side) (i : Nat) : Option Nat :=
  match (m.places s)[i]? with
  | some g => if m.held g then none else some g
  | none => none

/-- No crossing was taken and left unacknowledged. -/
def Mix.settled (m : Mix) : Bool :=
  (m.outA ++ m.outB).all (fun c => decide (c.state ≠ .taken))

/-- Place one entry of guest `s`: the state after it and the events it stands
    for, or nothing when it cannot be placed here. -/
def Mix.place (m : Mix) (s : Side) : Note → Option (Mix × List Event)
  | .did (.fresh i n) => (m.free s i).map fun g => (m, [.fresh g n])
  | .did (.spawn i) => (m.free s i).map fun g => (m.grow s, [.spawn g])
  | .did (.comm i j) =>
    match m.free s i, m.free s j with
    | some g, some h => some (m, [.comm g h])
    | _, _ => none
  | .did (.answer i x) => (m.free s i).map fun g => (m, [.answer g x])
  | .out i k =>
    match m.free s i with
    | some g =>
      if k = (m.outs s).length then some (m.setOuts s (m.outs s ++ [⟨g, .offered⟩]), [])
      else none
    | none => none
  | .spawnIn k =>
    match (m.outs s.other)[k]? with
    | some ⟨g, .offered⟩ =>
      some ((m.setOuts s.other ((m.outs s.other).set k ⟨g, .taken⟩)).grow s, [.spawn g])
    | _ => none
  | .sendIn k j =>
    match (m.outs s.other)[k]?, m.free s j with
    | some ⟨g, .offered⟩, some h =>
      some (m.setOuts s.other ((m.outs s.other).set k ⟨g, .taken⟩), [.comm g h])
    | _, _ => none
  | .ack k i =>
    match (m.outs s)[k]?, (m.places s)[i]? with
    | some ⟨g, .taken⟩, some g' =>
      if g = g' then some (m.setOuts s ((m.outs s).set k ⟨g, .acked⟩), []) else none
    | _, _ => none
  | .held _ => some (m, [])
  | .full _ => some (m, [])

/-- Walk two logs: the head of `a` when it can be placed, otherwise the head
    of `b`. Gives the entries in the order placed, each with the events it
    stands for, and the last state. `fuel` is a bound on the entries left. -/
def mix : Nat → Mix → List Note → List Note → Option (List (Side × Note × List Event) × Mix)
  | _, m, [], [] => if m.settled then some ([], m) else none
  | 0, _, _, _ => none
  | fuel + 1, m, x :: xs, ys =>
    match m.place .a x with
    | some (m', evs) => (mix fuel m' xs ys).map fun r => ((.a, x, evs) :: r.1, r.2)
    | none =>
      match ys with
      | y :: ys' =>
        match m.place .b y with
        | some (m', evs) => (mix fuel m' (x :: xs) ys').map fun r => ((.b, y, evs) :: r.1, r.2)
        | none => none
      | [] => none
  | fuel + 1, m, [], y :: ys =>
    match m.place .b y with
    | some (m', evs) => (mix fuel m' [] ys).map fun r => ((.b, y, evs) :: r.1, r.2)
    | none => none

/-- The entries of two logs in the order the walk placed them, each with its
    events, and the last state. -/
def combineTrace (a b : List Note) : Option (List (Side × Note × List Event) × Mix) :=
  mix (a.length + b.length) Mix.first a b

/-- The events of a trace, in order. -/
def traceEvents (t : List (Side × Note × List Event)) : List Event := t.flatMap (·.2.2)

/-- The entries of a trace, in order. -/
def traceEntries (t : List (Side × Note × List Event)) : List (Side × Note) := t.map fun e => (e.1, e.2.1)

/-- The schedule two logs make, and the places it gave. -/
def combineMix (a b : List Note) : Option (List Event × Mix) :=
  (combineTrace a b).map fun r => (traceEvents r.1, r.2)

/-- The schedule two logs make. -/
def combine (a b : List Note) : Option (List Event) := (combineMix a b).map (·.1)

/-- The table as a relation, apart from the order the walk happens to choose:
    each step places the head of one log, the events are those `place` gives,
    in that order, and the last state is settled. `tr` is the entries in the
    order they were placed. -/
inductive Walk : Mix → List Note → List Note → List (Side × Note) → List Event → Mix → Prop where
  | done {m} (h : m.settled = true) : Walk m [] [] [] [] m
  | left {m m' x xs ys tr evs evs' last} (h : m.place .a x = some (m', evs))
      (rest : Walk m' xs ys tr evs' last) :
      Walk m (x :: xs) ys ((.a, x) :: tr) (evs ++ evs') last
  | right {m m' y xs ys tr evs evs' last} (h : m.place .b y = some (m', evs))
      (rest : Walk m' xs ys tr evs' last) :
      Walk m xs (y :: ys) ((.b, y) :: tr) (evs ++ evs') last

/-- `evs` is a schedule the table allows for the logs `a` and `b`. -/
def Merged (a b : List Note) (evs : List Event) : Prop :=
  ∃ tr last, Walk Mix.first a b tr evs last

/-- The entries of guest `s` among those placed, in the order placed. -/
def entriesOf (s : Side) (tr : List (Side × Note)) : List Note :=
  tr.filterMap fun p => if p.1 = s then some p.2 else none

/-- The crossing an entry takes, when it takes one. -/
def Note.taking : Note → Option Nat
  | .spawnIn k => some k
  | .sendIn k _ => some k
  | _ => none

/-- The crossings of the peer that guest `s` took, in the order placed. -/
def takenBy (s : Side) (tr : List (Side × Note)) : List Nat :=
  tr.filterMap fun p => if p.1 = s then p.2.taking else none

variable [Ops]

/-- The check: combine the logs, begin the program, and run the schedule,
    every turn with `budget` steps and `cells` cells. A record is accepted
    only when every event of the schedule happened. -/
def accept (cells budget : Nat) (p : Term) (a b : List Note) : Option (List Event × MConfig) :=
  match combine a b, beginIn cells budget p with
  | some evs, some c₀ =>
    match schedIn cells budget c₀ evs with
    | (_, cfg, .ran) => some (evs, cfg)
    | _ => none
  | _, _ => none

end Reflect
