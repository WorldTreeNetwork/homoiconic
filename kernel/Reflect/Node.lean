import Reflect.Log

/-!
A node: several processes (`Reflect.Channel`) whose schedule is a log
(`Reflect.Log`). An *op* is an event with an identifier. A node is a
configuration of processes together with the identifiers of the ops it has
acted on. Applying an op whose identifier the node has acted on changes
nothing; otherwise the event happens, as `Step` says, and the identifier is
recorded. An op whose event cannot happen has no next state: a log is the
record of what happened, and a list that holds such an op is not the log of any
run.

An event is also split here into the machine runs it needs and what the
configuration is once they have ended (`plan`). `Step` is exactly that
(`plan_step`, `step_plan`), so anything that runs the jobs of a plan and takes
the configuration the plan then gives has made the event happen.
-/
namespace Reflect

/-- An event with an identifier. -/
structure Op where
  id : Data
  event : Event

/-- The op made of a mark and an event as it is written, `d`, which `read`
    takes for the event `ev`: its identifier is the name `key` gives to the
    mark and `d` together. -/
def Op.seal (key : Data → Data) (mark d : Data) (ev : Event) : Op :=
  ⟨key (.arr [mark, d]), ev⟩

/-- `o` is the seal of some mark and some writing of its event. -/
def Op.Sealed (key : Data → Data) (read : Data → Option Event) (o : Op) : Prop :=
  ∃ mark d, read d = some o.event ∧ o = Op.seal key mark d o.event

/-- Processes, and the identifiers of the ops acted on, newest first. -/
structure Node (C R : Type) where
  cfg : Config C R
  seen : List Data

inductive Apply {C R : Type} (S : PSys C R) : Node C R → Op → Node C R → Prop where
  /-- The node has acted on this identifier. -/
  | repeated {n o} (h : o.id ∈ n.seen) : Apply S n o n
  /-- The event happens. -/
  | happen {n o cfg'} (h : o.id ∉ n.seen) (hs : Step S n.cfg o.event cfg') :
      Apply S n o ⟨cfg', o.id :: n.seen⟩

/-- A log applied op by op. -/
inductive Applied {C R : Type} (S : PSys C R) : Node C R → List Op → Node C R → Prop where
  | nil {n} : Applied S n [] n
  | cons {n o mid os n'} (h : Apply S n o mid) (rest : Applied S mid os n') :
      Applied S n (o :: os) n'

/-- The node of program `p` whose log is `ops`. -/
def Ran {C R : Type} (S : PSys C R) (p : Term) (ops : List Op) (n : Node C R) : Prop :=
  ∃ c₀, Begin S p c₀ ∧ Applied S ⟨c₀, []⟩ ops n

/-- The ops of a log that are the first with their identifier, given the
    identifiers `seen` before it. -/
def firstOps (seen : List Data) : List Op → List Op
  | [] => []
  | o :: os => if o.id ∈ seen then firstOps seen os else o :: firstOps (o.id :: seen) os

def Node.map {C R C' R' : Type} (f : R → R') (g : C → C') (n : Node C R) : Node C' R' :=
  ⟨n.cfg.map f g, n.seen⟩

/-- A machine run an event needs. -/
inductive Job (C : Type) where
  /-- Answer the request `c` with `a` and run to the next request or the end. -/
  | turn (c : C) (a : Data)
  /-- Begin a program and run it to its first request or its end. -/
  | start (t : Term)

def Job.Runs {C R : Type} (S : PSys C R) : Job C → Status C R → Prop
  | .turn c a, st => Turn S.toSys c a st
  | .start t, st => ∃ r, S.start t r ∧ Settle S.toSys r st

/-- The jobs run, one after another, to the statuses. -/
def Job.AllRun {C R : Type} (S : PSys C R) : List (Job C) → List (Status C R) → Prop
  | [], [] => True
  | j :: js, st :: sts => j.Runs S st ∧ Job.AllRun S js sts
  | _, _ => False

/-- The runs an event needs, in order, and the configuration once they have
    ended where the list says. `none`: the event cannot happen. -/
def plan {C R : Type} (cfg : Config C R) :
    Event → Option (List (Job C) × (List (Status C R) → Option (Config C R)))
  | .fresh i n =>
    match cfg.procs[i]? with
    | some ⟨.waiting c p, held⟩ =>
      match classify p with
      | .fresh =>
        if n ∈ cfg.names then none else
        some ([.turn c (.name n)], fun
          | [st] => some ⟨cfg.procs.set i ⟨st, n :: held⟩, n :: cfg.names⟩
          | _ => none)
      | _ => none
    | _ => none
  | .spawn i =>
    match cfg.procs[i]? with
    | some ⟨.waiting c p, held⟩ =>
      match classify p with
      | .spawn t arg =>
        some ([.start (.app t (.lit arg)), .turn c (.arr [])], fun
          | [child, st] =>
            some ⟨cfg.procs.set i ⟨st, held⟩ ++ [⟨child, grant held arg⟩], cfg.names⟩
          | _ => none)
      | _ => none
    | _ => none
  | .comm i j =>
    match cfg.procs[i]?, cfg.procs[j]? with
    | some ⟨.waiting c p, held⟩, some ⟨.waiting c' p', held'⟩ =>
      match classify p, classify p' with
      | .send ch v, .receive ch' =>
        if ch = ch' ∧ ch ∈ held ∧ ch ∈ held' then
          some ([.turn c (.arr []), .turn c' v], fun
            | [st, st'] =>
              some ⟨(cfg.procs.set i ⟨st, held⟩).set j ⟨st', gain held' (grant held v)⟩, cfg.names⟩
            | _ => none)
        else none
      | _, _ => none
    | _, _ => none
  | .answer i a =>
    match cfg.procs[i]? with
    | some ⟨.waiting c p, held⟩ =>
      match classify p with
      | .outside =>
        some ([.turn c a], fun
          | [st] => some ⟨cfg.procs.set i ⟨st, held⟩, cfg.names⟩
          | _ => none)
      | _ => none
    | _ => none

variable [Ops]

abbrev MNode := Node MValue MOutcome

/-- How a run through a log stops. `refused` and `unfinished` keep the ops that
    were applied and the node they led to. -/
inductive NodeStop where
  | ran : NodeStop
  | refused : Op → NodeStop
  | unfinished : Op → NodeStop

/-- Apply the ops in order on the machine, stopping at the first whose event
    does not go through. Gives the ops applied, repeats among them, the node
    after them, and how the run stopped. -/
def nodeRun (budget : Nat) : MNode → List Op → List Op × MNode × NodeStop
  | n, [] => ([], n, .ran)
  | n, o :: os =>
    if o.id ∈ n.seen then
      let r := nodeRun budget n os
      (o :: r.1, r.2)
    else
      match stepRun budget n.cfg o.event with
      | .ok cfg' =>
        let r := nodeRun budget ⟨cfg', o.id :: n.seen⟩ os
        (o :: r.1, r.2)
      | .refused => ([], n, .refused o)
      | .unfinished => ([], n, .unfinished o)

end Reflect
