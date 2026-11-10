import Reflect

open Reflect

-- Acceptance check for `add-requests`. It fails to compile until the theorems
-- exist with exactly these signatures, for every table of operations. This
-- file does not import a table.

-- Replay: what a program asks and how it ends is fixed by the program and the
-- answers.
example : ∀ [Ops] {p : Term} {answers asked asked' : List Data} {e e' : Ending Value Outcome},
    Interact p answers asked e → Interact p answers asked' e' → asked = asked' ∧ e = e' :=
  Reflect.interact_deterministic

-- Continuing a waiting program is running it from the start with the answer added.
example : ∀ [Ops] {p : Term} {c : Value} {a : Data} {o : Outcome}
    {as bs asked asked' : List Data} {e : Ending Value Outcome},
    Interact p as asked (.waiting c) → Direct [c] (resumeTerm a) o →
    Drive source o bs asked' e → Interact p (as ++ a :: bs) (asked ++ asked') e :=
  Reflect.interact_resume

example : ∀ [Ops] {p : Term} {x : Outcome} {as asked : List Data} (bs : List Data),
    Interact p as asked (.finished x) → Interact p (as ++ bs) asked (.finished x) :=
  Reflect.interact_extra

-- The interpreter asks what the program asks, in the same order.
example : ∀ [Ops] (p : Term) (answers asked : List Data) (e : Ending Value Outcome),
    Interact p answers asked e ↔
    InteractI p answers asked (e.map reifyOutcome reifyValue) :=
  Reflect.interact_reflective

example : ∀ [Ops] (p : Term) (answers asked : List Data) (e' : Ending Data Data),
    InteractI p answers asked e' →
    ∃ e, e' = e.map reifyOutcome reifyValue ∧ Interact p answers asked e :=
  Reflect.interact_coverage

-- The machine asks what the program asks, in the same order.
example : ∀ [Ops] (p : Term) (answers asked : List Data) (e : Ending Value Outcome),
    Interact p answers asked e ↔ InteractM p answers asked (e.map MP.injO MP.injV) :=
  Reflect.interact_machine

example : ∀ [Ops] (p : Term) (answers asked : List Data) (e' : Ending MValue MOutcome),
    InteractM p answers asked e' →
    ∃ e, e' = e.map MP.injO MP.injV ∧ Interact p answers asked e :=
  Reflect.interact_machine_exact

-- What the host's driver reports is true of the program.
example : ∀ [Ops] {budget : Nat} {p : Term} {answers asked : List Data} {x : MOutcome},
    converse budget p answers = (asked, .finished x) →
    ∃ o, x = MP.injO o ∧ Interact p answers asked (.finished o) :=
  Reflect.converse_finished

example : ∀ [Ops] {budget : Nat} {p : Term} {answers asked : List Data} {c : MValue},
    converse budget p answers = (asked, .waiting c) →
    ∃ v, c = MP.injV v ∧ Interact p answers asked (.waiting v) :=
  Reflect.converse_waiting

#print axioms Reflect.interact_deterministic
#print axioms Reflect.interact_resume
#print axioms Reflect.interact_extra
#print axioms Reflect.interact_reflective
#print axioms Reflect.interact_coverage
#print axioms Reflect.interact_machine
#print axioms Reflect.interact_machine_exact
#print axioms Reflect.converse_finished
#print axioms Reflect.converse_waiting
