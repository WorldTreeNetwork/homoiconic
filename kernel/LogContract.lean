import Reflect

open Reflect

-- Acceptance check for `add-event-log`. It fails to compile until the theorems
-- exist with exactly these signatures, for every table of operations. This
-- file does not import a table.

-- P13. The state of a VM is fixed by its program and its log.
example : ∀ [Ops] {p : Term} {log : List Entry} {a b : Vm Value Outcome},
    Logged sourceP p log a → Logged sourceP p log b → a = b :=
  Reflect.log_deterministic

-- P13. The state after a log is the state after any first part of it, carried
-- on through the rest.
example : ∀ [Ops] {p : Term} {l₁ l₂ : List Entry} {v : Vm Value Outcome},
    Logged sourceP p (l₁ ++ l₂) v ↔ ∃ s, Logged sourceP p l₁ s ∧ Replay source s l₂ v :=
  Reflect.log_prefix

-- P14. Handling an entry that is already in the log leaves the state as it is.
example : ∀ [Ops] {p : Term} {log : List Entry} {v v' : Vm Value Outcome} {e : Entry},
    Logged sourceP p log v → e ∈ log → (Handle source v e v' ↔ v' = v) :=
  Reflect.log_again

-- P14. An entry delivered again, anywhere later, changes nothing.
example : ∀ [Ops] {p : Term} {l₁ l₂ : List Entry} {e : Entry} {v : Vm Value Outcome},
    e ∈ l₁ → (Logged sourceP p (l₁ ++ e :: l₂) v ↔ Logged sourceP p (l₁ ++ l₂) v) :=
  Reflect.log_redeliver

-- P14. A log does what its first deliveries do, in their order.
example : ∀ [Ops] {p : Term} {log : List Entry} {v : Vm Value Outcome},
    Logged sourceP p log v ↔ Logged sourceP p (firsts [] log) v :=
  Reflect.log_once

-- A state reached by a first part of the log, given the whole log, reaches
-- what the whole log reaches from the start.
example : ∀ [Ops] {p : Term} {l₁ l₂ : List Entry} {s v : Vm Value Outcome},
    Logged sourceP p l₁ s →
    (Replay source s (l₁ ++ l₂) v ↔ Logged sourceP p (l₁ ++ l₂) v) :=
  Reflect.log_restart

-- A VM's run is a run of its program against the answers of the first
-- deliveries, in their order.
example : ∀ [Ops] {p : Term} {log : List Entry} {v : Vm Value Outcome},
    Logged sourceP p log v →
    ∃ asked, Interact p ((firsts [] log).map (·.answer)) asked v.status.ending :=
  Reflect.log_interact

-- Two sealed entries with one identifier are one entry, for every `key` that
-- gives different names to different data. That the kernel's `key`, a Blake3
-- hash, is such a function is not proved: it is the hypothesis here.
example : ∀ {key : Data → Data}, Function.Injective key → ∀ {e e' : Entry},
    e.Sealed key → e'.Sealed key → e.id = e'.id → e = e' :=
  Reflect.sealed_same

-- So in a sealed log no entry is passed over for a different one: every entry
-- is among the first deliveries.
example : ∀ {key : Data → Data}, Function.Injective key → ∀ {log : List Entry},
    (∀ e ∈ log, e.Sealed key) → ∀ {e : Entry}, e ∈ log → e ∈ firsts [] log :=
  Reflect.sealed_first

-- Where the host has accepted the signature, a link names the entry before
-- it. The signature itself is the hypothesis `signed`, not a kernel check.
example : ∀ {signed : Data → Data → Prop} {key : Data → Data} {prev : Data} {i : Nat}
    {mark answer : Data} {rest : List (Data × Data)} {parent : Data} {order : Option Nat},
    signedChain signed key prev i ((mark, answer) :: rest) →
    readLink mark = some (parent, order) →
    signed mark answer ∧ parent = prev ∧ orderHere order i :=
  Reflect.signed_parent

-- An entry is sealed by its construction.
example : ∀ (key : Data → Data) (mark answer : Data),
    (Entry.seal key mark answer).Sealed key :=
  fun _ mark _ => ⟨mark, rfl⟩

-- The machine handles a log as direct evaluation does.
example : ∀ [Ops] {p : Term} {log : List Entry} {v : Vm Value Outcome},
    Logged sourceP p log v → Logged machineP p log (v.map MP.injO MP.injV) :=
  Reflect.log_machine

example : ∀ [Ops] {p : Term} {log : List Entry} {w : MVm},
    Logged machineP p log w → ∃ v, Logged sourceP p log v ∧ w = v.map MP.injO MP.injV :=
  Reflect.log_machine_exact

-- The executable VM is a fold over the log, and the state it reports is true
-- of the program.
example : ∀ [Ops] (budget : Nat) (p : Term) (log : List Entry),
    vmRun budget p log = log.foldl (handleRun budget) (bootRun budget p) :=
  fun _ _ _ => rfl

example : ∀ [Ops] {budget : Nat} {p : Term} {log : List Entry} {w : MVm},
    vmRun budget p log = some w →
    ∃ v, Logged sourceP p log v ∧ w = v.map MP.injO MP.injV :=
  Reflect.vm_true

#print axioms Reflect.log_deterministic
#print axioms Reflect.log_prefix
#print axioms Reflect.log_again
#print axioms Reflect.log_redeliver
#print axioms Reflect.log_once
#print axioms Reflect.log_restart
#print axioms Reflect.log_interact
#print axioms Reflect.log_machine
#print axioms Reflect.log_machine_exact
#print axioms Reflect.vm_true
#print axioms Reflect.sealed_same
#print axioms Reflect.sealed_first
#print axioms Reflect.signed_parent
