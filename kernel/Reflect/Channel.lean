import Reflect.Request

/-!
Channels. Several programs run side by side as *processes* and talk over
*channels*, in the style of the pi-calculus: a channel is named by a name value
(`Data.name`, which carries a number), and a name can be sent over a channel. Nothing is added to the language. A process
is a program that makes requests (`Reflect.Request`), and four shapes of payload
are read here as channel requests:

  `[0]`                  make a new channel; the answer is its name
  `[1, name, message]`   send `message` on `name`; the answer is `[]`
  `[2, name]`            receive on `name`; the answer is the message
  `[3, program, start]`  start `program`, a quoted program, on the data `start`
                         as a new process; the answer is `[]`

`name` is a name value. Every other payload is a request to the outside,
answered as before; `[1, n, message]` and `[2, n]` with `n` a plain number are
among them.

A send and a receive on one name meet: there is no queue. What happens next is
chosen by a *schedule*, a list of events, and a new name is supplied by the
event that makes it. The definitions here say what each event does; they do not
choose.

Each process *holds* a list of names, kept as their numbers. It holds a name it
made, a name its starter held that occurs as a name value in the data it was
started on, and a name its sender held that occurs as a name value in a message
it received. A plain number hands over nothing. A send or a receive on a name
the process does not hold never happens. A name value is not a key: holding is
this list.
-/
namespace Reflect

mutual
  /-- Does the name with number `n` occur in the data, as a name value? A
      plain number is not a name. -/
  def Data.mentions : Data → Nat → Bool
    | .name k, n => k == n
    | .nat _, _ => false
    | .text _, _ => false
    | .arr xs, n => mentionsAny xs n
  def mentionsAny : List Data → Nat → Bool
    | [], _ => false
    | x :: xs, n => x.mentions n || mentionsAny xs n
end

/-- Whether a name occurs in any of the data, which waits in a list: nothing
    here recurses on how deep the data is nested (`homoiconic-q59.72`). -/
def mentionsGo (n : Nat) : List Data → Bool
  | [] => false
  | .name k :: ds => k == n || mentionsGo n ds
  | .nat _ :: ds => mentionsGo n ds
  | .text _ :: ds => mentionsGo n ds
  | .arr xs :: ds => mentionsGo n (xs ++ ds)
termination_by ds => Data.sizeList ds
decreasing_by all_goals simp_wf; all_goals (simp only [Data.sizeList, Data.size, Data.sizeList_append]; omega)

theorem mentionsAny_append (xs ys : List Data) (n : Nat) :
    mentionsAny (xs ++ ys) n = (mentionsAny xs n || mentionsAny ys n) := by
  induction xs with
  | nil => simp [mentionsAny]
  | cons x xs ih => simp [mentionsAny, ih, Bool.or_assoc]

theorem mentionsGo_eq (n : Nat) (ds : List Data) : mentionsGo n ds = mentionsAny ds n := by
  induction ds using mentionsGo.induct with
  | case1 => simp [mentionsGo, mentionsAny]
  | case2 k ds ih => simp [mentionsGo, mentionsAny, Data.mentions, ih]
  | case3 k ds ih => simp [mentionsGo, mentionsAny, Data.mentions, ih]
  | case4 k ds ih => simp [mentionsGo, mentionsAny, Data.mentions, ih]
  | case5 xs ds ih => simp [mentionsGo, mentionsAny, Data.mentions, ih, mentionsAny_append]

/-- `Data.mentions`, as a walk; the compiler runs it (`mentions_eq_walk`). -/
def Data.mentionsWalk (d : Data) (n : Nat) : Bool := mentionsGo n [d]

@[csimp] theorem mentions_eq_walk : @Data.mentions = @Data.mentionsWalk := by
  funext d n; simp [Data.mentionsWalk, mentionsGo_eq, mentionsAny]

/-- The names among `held` that occur in `d`: what handing over `d` hands over. -/
def grant (held : List Nat) (d : Data) : List Nat := held.filter (d.mentions ·)

/-- Add what is handed over, leaving out what is already held. -/
def gain (held' handed : List Nat) : List Nat :=
  handed.filter (fun n => !held'.contains n) ++ held'

/-- What a payload asks for. -/
inductive Req where
  | fresh : Req
  | send : Nat → Data → Req
  | receive : Nat → Req
  | spawn : Term → Data → Req
  | outside : Req

/-- Read a payload. A start request whose program is not the data form of a
    program is a request to the outside. -/
def classify : Data → Req
  | .arr [.nat 0] => .fresh
  | .arr [.nat 1, .name ch, v] => .send ch v
  | .arr [.nat 2, .name ch] => .receive ch
  | .arr [.nat 3, prog, arg] =>
    match unreify prog with
    | some t => .spawn t arg
    | none => .outside
  | _ => .outside

/-- A way of evaluating that can also begin a program. -/
structure PSys (C R : Type) extends Sys C R where
  /-- Evaluate a term with nothing bound. -/
  start : Term → R → Prop

/-- Where a process stands between events: waiting on a request whose payload
    has been read, or finished. -/
inductive Status (C R : Type) where
  | waiting : C → Data → Status C R
  | finished : R → Status C R

structure Proc (C R : Type) where
  status : Status C R
  /-- The names the process may use. -/
  held : List Nat

/-- All the processes, in the order they were started, and every name made so
    far. A process is known by its place in the list. -/
structure Config (C R : Type) where
  procs : List (Proc C R)
  names : List Nat

/-- Where the result of a turn leaves a process. The cases are `Drive`'s: a
    result that is not a function finishes, and every function is read as a
    request, whose payload must be data. -/
inductive Settle {C R : Type} (S : Sys C R) : R → Status C R → Prop where
  | stop {r} (h : S.fn r = none) : Settle S r (.finished r)
  | payloadFails {r c r'} (h : S.fn r = some c) (hp : S.eval c payloadTerm r')
      (hf : S.fn r' = none) (hd : S.dat r' = none) : Settle S r (.finished r')
  | payloadFunction {r c r' c'} (h : S.fn r = some c) (hp : S.eval c payloadTerm r')
      (hf : S.fn r' = some c') : Settle S r (.finished S.wrong)
  | wait {r c r' p} (h : S.fn r = some c) (hp : S.eval c payloadTerm r')
      (hd : S.dat r' = some p) : Settle S r (.waiting c p)

/-- Answer the request `c` with `a` and run to the next request or the end. -/
def Turn {C R : Type} (S : Sys C R) (c : C) (a : Data) (st : Status C R) : Prop :=
  ∃ r, S.eval c (resumeTerm a) r ∧ Settle S r st

/-- One thing that happens. Processes are named by their place. -/
inductive Event where
  /-- Process `i` asked for a new channel and is given the name `n`. -/
  | fresh (i n : Nat) : Event
  /-- Process `i` asked to start a process, and it is started. -/
  | spawn (i : Nat) : Event
  /-- Process `i` is sending and process `j` receiving on one name, and they meet. -/
  | comm (i j : Nat) : Event
  /-- Process `i` asked the outside and is answered `a`. -/
  | answer (i : Nat) (a : Data) : Event
  deriving Repr, BEq

/-- What an event does. An event with no rule here cannot happen. -/
inductive Step {C R : Type} (S : PSys C R) : Config C R → Event → Config C R → Prop where
  | fresh {cfg i n c p held st} (hi : cfg.procs[i]? = some ⟨.waiting c p, held⟩)
      (hq : classify p = .fresh) (hn : n ∉ cfg.names)
      (ht : Turn S.toSys c (.name n) st) :
      Step S cfg (.fresh i n) ⟨cfg.procs.set i ⟨st, n :: held⟩, n :: cfg.names⟩
  | spawn {cfg i c p held t arg r child st} (hi : cfg.procs[i]? = some ⟨.waiting c p, held⟩)
      (hq : classify p = .spawn t arg) (hs : S.start (.app t (.lit arg)) r)
      (hc : Settle S.toSys r child) (ht : Turn S.toSys c (.arr []) st) :
      Step S cfg (.spawn i)
        ⟨cfg.procs.set i ⟨st, held⟩ ++ [⟨child, grant held arg⟩], cfg.names⟩
  | comm {cfg i j c p held c' p' held' ch v st st'}
      (hi : cfg.procs[i]? = some ⟨.waiting c p, held⟩)
      (hj : cfg.procs[j]? = some ⟨.waiting c' p', held'⟩)
      (hq : classify p = .send ch v) (hq' : classify p' = .receive ch)
      (hh : ch ∈ held) (hh' : ch ∈ held')
      (ht : Turn S.toSys c (.arr []) st) (ht' : Turn S.toSys c' v st') :
      Step S cfg (.comm i j)
        ⟨(cfg.procs.set i ⟨st, held⟩).set j ⟨st', gain held' (grant held v)⟩, cfg.names⟩
  | answer {cfg i a c p held st} (hi : cfg.procs[i]? = some ⟨.waiting c p, held⟩)
      (hq : classify p = .outside) (ht : Turn S.toSys c a st) :
      Step S cfg (.answer i a) ⟨cfg.procs.set i ⟨st, held⟩, cfg.names⟩

/-- A schedule, event by event. -/
inductive Sched {C R : Type} (S : PSys C R) : Config C R → List Event → Config C R → Prop where
  | nil {cfg} : Sched S cfg [] cfg
  | cons {cfg ev mid evs cfg'} (h : Step S cfg ev mid) (rest : Sched S mid evs cfg') :
      Sched S cfg (ev :: evs) cfg'

/-- One process, the program, holding no name, and no name made. -/
def Begin {C R : Type} (S : PSys C R) (p : Term) (cfg : Config C R) : Prop :=
  ∃ r st, S.start p r ∧ Settle S.toSys r st ∧ cfg = ⟨[⟨st, []⟩], []⟩

/-- A program run as the first process, through a schedule. -/
def Network {C R : Type} (S : PSys C R) (p : Term) (evs : List Event) (cfg : Config C R) : Prop :=
  ∃ c₀, Begin S p c₀ ∧ Sched S c₀ evs cfg

def Status.map {C R C' R' : Type} (f : R → R') (g : C → C') : Status C R → Status C' R'
  | .waiting c p => .waiting (g c) p
  | .finished r => .finished (f r)

def Proc.map {C R C' R' : Type} (f : R → R') (g : C → C') (q : Proc C R) : Proc C' R' :=
  ⟨q.status.map f g, q.held⟩

def Config.map {C R C' R' : Type} (f : R → R') (g : C → C') (cfg : Config C R) : Config C' R' :=
  ⟨cfg.procs.map (Proc.map f g), cfg.names⟩

variable [Ops]

/-- Direct evaluation. -/
def sourceP : PSys Value Outcome where
  toSys := source
  start t o := Direct [] t o

/-- The machine. -/
def machineP : PSys MValue MOutcome where
  toSys := machine
  start t w := ∃ n, run n (load (compile t)) = .halted w

/-- The interpreter, on data: a program is begun by `interp` on its data
    form, and every turn is evaluated by the interpreter. Results are outcomes
    as data, and a waiting process is held as a closure as data. -/
def interpretedP : PSys Data Data where
  toSys := interpreted
  start t w := Direct [] (.app interp (.lit (reify t))) (.value (.data w))

/-! The executable scheduler, on the machine. Every machine run gets `budget`
    steps and may make `cells` cells (`runTurnIn`): beginning a program,
    reading a payload, and running the rest on an answer. Every driver runs
    them at `turnSpace` (`settleRun`, `turnRun`, `stepRun`, `schedRun`,
    `beginRun`); the two guests of a crossing agree on a turn space of their
    own. -/

/-- `none`: a machine run did not halt within the budget, or within the cells
    a turn may make (`runTurn`). -/
def settleIn (cells budget : Nat) : MOutcome → Option (Status MValue MOutcome)
  | .value (.closure k e) =>
    match runTurnIn cells budget (.running (compile payloadTerm) [.closure k e] [] []) with
    | .halted (.value (.data p)) => some (.waiting (.closure k e) p)
    | .halted (.value (.closure _ _)) => some (.finished .wrong)
    | .halted w => some (.finished w)
    | _ => none
  | w => some (.finished w)

def turnIn (cells budget : Nat) (c : MValue) (a : Data) : Option (Status MValue MOutcome) :=
  match runTurnIn cells budget (.running (compile (resumeTerm a)) [c] [] []) with
  | .halted w => settleIn cells budget w
  | _ => none

abbrev MConfig := Config MValue MOutcome

/-- What trying an event gives: the next configuration, a refusal because the
    event cannot happen, or a machine run that did not halt in its budget or
    in the cells a turn may make. -/
inductive Tried where
  | ok : MConfig → Tried
  | refused : Tried
  | unfinished : Tried

def stepIn (cells budget : Nat) (cfg : MConfig) : Event → Tried
  | .fresh i n =>
    match cfg.procs[i]? with
    | some ⟨.waiting c p, held⟩ =>
      match classify p with
      | .fresh =>
        if cfg.names.contains n then .refused else
        match turnIn cells budget c (.name n) with
        | some st => .ok ⟨cfg.procs.set i ⟨st, n :: held⟩, n :: cfg.names⟩
        | none => .unfinished
      | _ => .refused
    | _ => .refused
  | .spawn i =>
    match cfg.procs[i]? with
    | some ⟨.waiting c p, held⟩ =>
      match classify p with
      | .spawn t arg =>
        match runTurnIn cells budget (load (compile (.app t (.lit arg)))) with
        | .halted w =>
          match settleIn cells budget w, turnIn cells budget c (.arr []) with
          | some child, some st =>
            .ok ⟨cfg.procs.set i ⟨st, held⟩ ++ [⟨child, grant held arg⟩], cfg.names⟩
          | _, _ => .unfinished
        | _ => .unfinished
      | _ => .refused
    | _ => .refused
  | .comm i j =>
    match cfg.procs[i]?, cfg.procs[j]? with
    | some ⟨.waiting c p, held⟩, some ⟨.waiting c' p', held'⟩ =>
      match classify p, classify p' with
      | .send ch v, .receive ch' =>
        if ch == ch' && held.contains ch && held'.contains ch then
          match turnIn cells budget c (.arr []), turnIn cells budget c' v with
          | some st, some st' =>
            .ok ⟨(cfg.procs.set i ⟨st, held⟩).set j ⟨st', gain held' (grant held v)⟩, cfg.names⟩
          | _, _ => .unfinished
        else .refused
      | _, _ => .refused
    | _, _ => .refused
  | .answer i a =>
    match cfg.procs[i]? with
    | some ⟨.waiting c p, held⟩ =>
      match classify p with
      | .outside =>
        match turnIn cells budget c a with
        | some st => .ok ⟨cfg.procs.set i ⟨st, held⟩, cfg.names⟩
        | none => .unfinished
      | _ => .refused
    | _ => .refused

/-- How a run through a schedule stops. `refused` and `unfinished` keep the
    events that did happen and the configuration they led to. -/
inductive Stopped where
  | ran : Stopped
  | refused : Event → Stopped
  | unfinished : Event → Stopped

/-- Run the events in order, stopping at the first that does not go through.
    Gives the events that happened, the configuration after them, and how the
    run stopped. -/
def schedIn (cells budget : Nat) : MConfig → List Event → List Event × MConfig × Stopped
  | cfg, [] => ([], cfg, .ran)
  | cfg, ev :: evs =>
    match stepIn cells budget cfg ev with
    | .ok mid =>
      let r := schedIn cells budget mid evs
      (ev :: r.1, r.2)
    | .refused => ([], cfg, .refused ev)
    | .unfinished => ([], cfg, .unfinished ev)

/-- `schedIn` with the events that happened so far in `acc`, newest first: a
    loop, not a call for each event (`homoiconic-q59.78`). -/
def schedGo (cells budget : Nat) (acc : List Event) : MConfig → List Event → List Event × MConfig × Stopped
  | cfg, [] => (acc.reverse, cfg, .ran)
  | cfg, ev :: evs =>
    match stepIn cells budget cfg ev with
    | .ok mid => schedGo cells budget (ev :: acc) mid evs
    | .refused => (acc.reverse, cfg, .refused ev)
    | .unfinished => (acc.reverse, cfg, .unfinished ev)

theorem schedGo_eq (cells budget : Nat) : ∀ (evs : List Event) (cfg : MConfig) (acc : List Event),
    schedGo cells budget acc cfg evs =
      (acc.reverse ++ (schedIn cells budget cfg evs).1, (schedIn cells budget cfg evs).2)
  | [], cfg, acc => by simp [schedGo, schedIn]
  | ev :: evs, cfg, acc => by
    rw [schedGo, schedIn]
    cases stepIn cells budget cfg ev with
    | ok mid => simp only []; rw [schedGo_eq cells budget evs mid]; simp
    | refused => simp
    | unfinished => simp

def schedInWalk (cells budget : Nat) (cfg : MConfig) (evs : List Event) : List Event × MConfig × Stopped :=
  schedGo cells budget [] cfg evs

omit [Ops] in
@[csimp] theorem schedIn_eq_walk : @schedIn = @schedInWalk := by
  funext inst cells budget cfg evs
  simp [schedInWalk, schedGo_eq]

/-- The first configuration, on the machine. `none`: a run did not halt. -/
def beginIn (cells budget : Nat) (p : Term) : Option MConfig :=
  match runTurnIn cells budget (load (compile p)) with
  | .halted w =>
    match settleIn cells budget w with
    | some st => some ⟨[⟨st, []⟩], []⟩
    | none => none
  | _ => none

/-- The runs above at `turnSpace`, the turn space of every driver but a
    crossing. -/
def settleRun (budget : Nat) : MOutcome → Option (Status MValue MOutcome) := settleIn turnSpace budget
def turnRun (budget : Nat) : MValue → Data → Option (Status MValue MOutcome) := turnIn turnSpace budget
def stepRun (budget : Nat) : MConfig → Event → Tried := stepIn turnSpace budget
def schedRun (budget : Nat) : MConfig → List Event → List Event × MConfig × Stopped :=
  schedIn turnSpace budget
def beginRun (budget : Nat) : Term → Option MConfig := beginIn turnSpace budget

/-! Choosing. `pick` is one way to choose the next event: the first process, in
    order, whose request has what it needs in the configuration. It does not run
    the machine, so an event it offers may still not halt within a budget, and
    it never offers an answer from outside. It is a convenience for making a schedule; the
    meaning of the schedule it makes is `Step`'s. -/

/-- A name not made yet. -/
def nextName (names : List Nat) : Nat := names.foldl (fun m n => max m (n + 1)) 0

/-- The place of the first process that `ok` accepts. -/
def findProc (ok : Proc MValue MOutcome → Bool) (procs : List (Proc MValue MOutcome)) :
    Option Nat :=
  let i := procs.findIdx ok
  if i < procs.length then some i else none

def sendsOn (ch : Nat) (q : Proc MValue MOutcome) : Bool :=
  match q.status with
  | .waiting _ p =>
    match classify p with
    | .send ch' _ => ch == ch' && q.held.contains ch
    | _ => false
  | _ => false

def receivesOn (ch : Nat) (q : Proc MValue MOutcome) : Bool :=
  match q.status with
  | .waiting _ p =>
    match classify p with
    | .receive ch' => ch == ch' && q.held.contains ch
    | _ => false
  | _ => false

/-- What process `i` can do now, if anything. A request to the outside is left
    waiting: only a schedule can answer it. -/
def offer (cfg : MConfig) (i : Nat) (q : Proc MValue MOutcome) : Option Event :=
  match q.status with
  | .waiting _ p =>
    match classify p with
    | .fresh => some (.fresh i (nextName cfg.names))
    | .spawn _ _ => some (.spawn i)
    | .send ch _ =>
      if q.held.contains ch then (findProc (receivesOn ch) cfg.procs).map (Event.comm i ·)
      else none
    | .receive ch =>
      if q.held.contains ch then (findProc (sendsOn ch) cfg.procs).map (Event.comm · i)
      else none
    | .outside => none
  | .finished _ => none

def pickFrom (cfg : MConfig) : Nat → List (Proc MValue MOutcome) → Option Event
  | _, [] => none
  | i, q :: qs =>
    match offer cfg i q with
    | some ev => some ev
    | none => pickFrom cfg (i + 1) qs

def pick (cfg : MConfig) : Option Event := pickFrom cfg 0 cfg.procs

/-- Choose and run events until nothing can happen or `limit` events have.
    The last part is true when it stopped at the limit with more to do. -/
def autoRun (budget : Nat) : Nat → MConfig → List Event × MConfig × Stopped × Bool
  | 0, cfg => ([], cfg, .ran, (pick cfg).isSome)
  | limit + 1, cfg =>
    match pick cfg with
    | none => ([], cfg, .ran, false)
    | some ev =>
      match stepRun budget cfg ev with
      | .ok mid =>
        let r := autoRun budget limit mid
        (ev :: r.1, r.2)
      | .refused => ([], cfg, .refused ev, false)
      | .unfinished => ([], cfg, .unfinished ev, false)

/-- `autoRun` with the events that happened so far in `acc`, newest first: a
    loop (`homoiconic-q59.78`). -/
def autoGo (budget : Nat) (acc : List Event) : Nat → MConfig → List Event × MConfig × Stopped × Bool
  | 0, cfg => (acc.reverse, cfg, .ran, (pick cfg).isSome)
  | limit + 1, cfg =>
    match pick cfg with
    | none => (acc.reverse, cfg, .ran, false)
    | some ev =>
      match stepRun budget cfg ev with
      | .ok mid => autoGo budget (ev :: acc) limit mid
      | .refused => (acc.reverse, cfg, .refused ev, false)
      | .unfinished => (acc.reverse, cfg, .unfinished ev, false)

theorem autoGo_eq (budget : Nat) : ∀ (limit : Nat) (cfg : MConfig) (acc : List Event),
    autoGo budget acc limit cfg =
      (acc.reverse ++ (autoRun budget limit cfg).1, (autoRun budget limit cfg).2)
  | 0, cfg, acc => by simp [autoGo, autoRun]
  | limit + 1, cfg, acc => by
    rw [autoGo, autoRun]
    cases pick cfg with
    | none => simp
    | some ev =>
      simp only []
      cases stepRun budget cfg ev with
      | ok mid => simp only []; rw [autoGo_eq budget limit mid]; simp
      | refused => simp
      | unfinished => simp

def autoRunWalk (budget limit : Nat) (cfg : MConfig) : List Event × MConfig × Stopped × Bool :=
  autoGo budget [] limit cfg

omit [Ops] in
@[csimp] theorem autoRun_eq_walk : @autoRun = @autoRunWalk := by
  funext inst budget limit cfg
  simp [autoRunWalk, autoGo_eq]

end Reflect
