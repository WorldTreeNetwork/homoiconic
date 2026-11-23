import Reflect

open Reflect

-- Acceptance check for `add-channels`. It fails to compile until the theorems
-- exist with exactly these signatures, for every table of operations. This
-- file does not import a table.

-- Replay: where a program gets to is fixed by the program and the schedule.
-- The names made and the answers from outside are events of the schedule.
example : ∀ [Ops] {p : Term} {evs : List Event} {a b : Config Value Outcome},
    Network sourceP p evs a → Network sourceP p evs b → a = b :=
  Reflect.network_deterministic

-- A send and a receive meet only on a name both processes hold.
example : ∀ {C R : Type} {S : PSys C R} {cfg cfg' : Config C R} {i j : Nat},
    Step S cfg (.comm i j) cfg' →
    ∃ ch v c p held c' p' held',
      cfg.procs[i]? = some ⟨.waiting c p, held⟩ ∧ classify p = .send ch v ∧ ch ∈ held ∧
      cfg.procs[j]? = some ⟨.waiting c' p', held'⟩ ∧ classify p' = .receive ch ∧ ch ∈ held' :=
  Reflect.Step.comm_held

-- Where a held name comes from: held before, made for this process by this
-- event, or handed over by a process that held it, in a message or a start.
example : ∀ {C R : Type} {S : PSys C R} {cfg cfg' : Config C R} {ev : Event},
    Step S cfg ev cfg' → ∀ {k n : Nat} {q : Proc C R},
    cfg'.procs[k]? = some q → n ∈ q.held →
    (∃ q₀, cfg.procs[k]? = some q₀ ∧ n ∈ q₀.held) ∨ ev = .fresh k n ∨
    (∃ i q₀, cfg.procs[i]? = some q₀ ∧ n ∈ q₀.held ∧ (ev = .comm i k ∨ ev = .spawn i)) :=
  fun h => Reflect.Step.held_from h

-- Every name a process of a program holds was made by an event of the schedule.
example : ∀ {C R : Type} {S : PSys C R} {p : Term} {evs : List Event} {cfg : Config C R},
    Network S p evs cfg → ∀ {k n : Nat} {q : Proc C R},
    cfg.procs[k]? = some q → n ∈ q.held → ∃ i, Event.fresh i n ∈ evs :=
  fun h => Reflect.Network.held_issued h

-- No process of a program holds a name twice.
example : ∀ {C R : Type} {S : PSys C R} {p : Term} {evs : List Event} {cfg : Config C R},
    Network S p evs cfg → ∀ {k : Nat} {q : Proc C R},
    cfg.procs[k]? = some q → q.held.Nodup :=
  fun h => Reflect.Network.held_nodup h

-- The machine runs a schedule as direct evaluation does.
example : ∀ [Ops] {p : Term} {evs : List Event} {cfg : Config Value Outcome},
    Network sourceP p evs cfg → Network machineP p evs (cfg.map MP.injO MP.injV) :=
  Reflect.network_machine

example : ∀ [Ops] {p : Term} {evs : List Event} {mc : MConfig},
    Network machineP p evs mc →
    ∃ cfg, Network sourceP p evs cfg ∧ mc = cfg.map MP.injO MP.injV :=
  Reflect.network_machine_exact

-- The interpreter on data runs a schedule as the program does: every
-- evaluation of the run is `interp`, or its `evalTerm`, on a data form.
example : ∀ [Ops] (p : Term) (evs : List Event) (cfg : Config Value Outcome),
    Network sourceP p evs cfg ↔
    Network interpretedP p evs (cfg.map reifyOutcome reifyValue) :=
  Reflect.network_reflective

example : ∀ [Ops] {p : Term} {evs : List Event} {ic : Config Data Data},
    Network interpretedP p evs ic →
    ∃ cfg, Network sourceP p evs cfg ∧ ic = cfg.map reifyOutcome reifyValue :=
  Reflect.network_interpreted_exact

-- What the host's scheduler reports is true of the program, however it stopped.
example : ∀ [Ops] {budget : Nat} {p : Term} {c₀ : MConfig} (evs : List Event),
    beginRun budget p = some c₀ →
    ∃ cfg, Network sourceP p (schedRun budget c₀ evs).1 cfg ∧
      (schedRun budget c₀ evs).2.1 = cfg.map MP.injO MP.injV :=
  Reflect.replay_true

example : ∀ [Ops] {budget : Nat} {p : Term} {c₀ : MConfig} (limit : Nat),
    beginRun budget p = some c₀ →
    ∃ cfg, Network sourceP p (autoRun budget limit c₀).1 cfg ∧
      (autoRun budget limit c₀).2.1 = cfg.map MP.injO MP.injV :=
  Reflect.auto_true

#print axioms Reflect.network_deterministic
#print axioms Reflect.Step.comm_held
#print axioms Reflect.Step.held_from
#print axioms Reflect.Network.held_issued
#print axioms Reflect.Network.held_nodup
#print axioms Reflect.network_machine
#print axioms Reflect.network_machine_exact
#print axioms Reflect.network_reflective
#print axioms Reflect.network_interpreted_exact
#print axioms Reflect.replay_true
#print axioms Reflect.auto_true
