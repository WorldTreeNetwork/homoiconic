import Reflect

open Reflect

-- Acceptance check for `add-logged-processes`. It fails to compile until the
-- theorems exist with exactly these signatures, for every table of operations.
-- This file does not import a table.

-- The node a program reaches is fixed by the program and the log.
example : ∀ [Ops] {p : Term} {ops : List Op} {a b : Node Value Outcome},
    Ran sourceP p ops a → Ran sourceP p ops b → a = b :=
  Reflect.node_deterministic

-- The node after a log is the node after any first part of it, carried on
-- through the rest.
example : ∀ [Ops] {p : Term} {l₁ l₂ : List Op} {n : Node Value Outcome},
    Ran sourceP p (l₁ ++ l₂) n ↔ ∃ s, Ran sourceP p l₁ s ∧ Applied sourceP s l₂ n :=
  Reflect.node_prefix

-- Applying an op that is already in the log leaves the node as it is.
example : ∀ [Ops] {p : Term} {ops : List Op} {n n' : Node Value Outcome} {o : Op},
    Ran sourceP p ops n → o ∈ ops → (Apply sourceP n o n' ↔ n' = n) :=
  Reflect.node_again

-- An op delivered again, anywhere later, changes nothing.
example : ∀ [Ops] {p : Term} {l₁ l₂ : List Op} {o : Op} {n : Node Value Outcome},
    o ∈ l₁ → (Ran sourceP p (l₁ ++ o :: l₂) n ↔ Ran sourceP p (l₁ ++ l₂) n) :=
  Reflect.node_redeliver

-- A node reached by a first part of the log, given the whole log, reaches
-- what the whole log reaches from the start.
example : ∀ [Ops] {p : Term} {l₁ l₂ : List Op} {s n : Node Value Outcome},
    Ran sourceP p l₁ s →
    (Applied sourceP s (l₁ ++ l₂) n ↔ Ran sourceP p (l₁ ++ l₂) n) :=
  Reflect.node_restart

-- A node's processes are where the schedule of the log's first deliveries
-- leads the program, so the channel theorems hold of them.
example : ∀ [Ops] {p : Term} {ops : List Op} {n : Node Value Outcome},
    Ran sourceP p ops n → Network sourceP p ((firstOps [] ops).map (·.event)) n.cfg :=
  Reflect.node_network

-- The machine applies a log as direct evaluation does.
example : ∀ [Ops] {p : Term} {ops : List Op} {n : Node Value Outcome},
    Ran sourceP p ops n → Ran machineP p ops (n.map MP.injO MP.injV) :=
  Reflect.node_machine

example : ∀ [Ops] {p : Term} {ops : List Op} {w : MNode},
    Ran machineP p ops w → ∃ n, Ran sourceP p ops n ∧ w = n.map MP.injO MP.injV :=
  Reflect.node_machine_exact

-- What the executable node reports is true of the program, however it stopped.
example : ∀ [Ops] {budget : Nat} {p : Term} {c₀ : MConfig} (ops : List Op),
    beginRun budget p = some c₀ →
    ∃ n, Ran sourceP p (nodeRun budget ⟨c₀, []⟩ ops).1 n ∧
      (nodeRun budget ⟨c₀, []⟩ ops).2.1 = n.map MP.injO MP.injV :=
  Reflect.node_true

-- An event is the machine runs of its plan and the configuration the plan
-- then gives: both directions, for every way of evaluating.
example : ∀ {C R : Type} {S : PSys C R} {cfg cfg' : Config C R} {ev : Event}
    {jobs : List (Job C)} {done : List (Status C R) → Option (Config C R)}
    {sts : List (Status C R)},
    plan cfg ev = some (jobs, done) → Job.AllRun S jobs sts → done sts = some cfg' →
    Step S cfg ev cfg' :=
  Reflect.plan_step

example : ∀ {C R : Type} {S : PSys C R} {cfg cfg' : Config C R} {ev : Event},
    Step S cfg ev cfg' →
    ∃ jobs done sts, plan cfg ev = some (jobs, done) ∧ Job.AllRun S jobs sts ∧
      done sts = some cfg' :=
  Reflect.step_plan

#print axioms Reflect.node_deterministic
#print axioms Reflect.node_prefix
#print axioms Reflect.node_again
#print axioms Reflect.node_redeliver
#print axioms Reflect.node_restart
#print axioms Reflect.node_network
#print axioms Reflect.node_machine
#print axioms Reflect.node_machine_exact
#print axioms Reflect.node_true
#print axioms Reflect.plan_step
#print axioms Reflect.step_plan
