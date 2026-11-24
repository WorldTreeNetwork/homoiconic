import Reflect

open Reflect

-- Acceptance check for `add-recorded-crossing`. It fails to compile until the
-- theorems exist with exactly these signatures, for every table of
-- operations. This file does not import a table.

-- A record the check accepts is a run of the one-machine network: the
-- schedule the two guests' logs make is one the table allows, and it leads
-- the program, by direct evaluation, to a configuration whose compiled form
-- is the one the check reports. So every channel theorem holds of it.
example : ∀ [Ops] {budget : Nat} {p : Term} {a b : List Note} {evs : List Event} {cfg : MConfig},
    accept budget p a b = some (evs, cfg) →
    Merged a b evs ∧ ∃ c, Network sourceP p evs c ∧ cfg = c.map MP.injO MP.injV :=
  Reflect.accepted_network

-- The walk does only what the table allows.
example : ∀ {a b : List Note} {evs : List Event}, combine a b = some evs → Merged a b evs :=
  Reflect.combine_merged

-- A schedule the table allows keeps each log whole and in its order: the
-- entries of each guest among those placed, in the order placed, are its log.
example : ∀ {a b : List Note} {evs : List Event}, Merged a b evs →
    ∃ tr, entriesOf .a tr = a ∧ entriesOf .b tr = b :=
  Reflect.merged_exact

-- And in it no crossing is taken twice: the crossings each guest took are all
-- different.
example : ∀ {a b : List Note} {evs : List Event}, Merged a b evs →
    ∃ tr, entriesOf .a tr = a ∧ entriesOf .b tr = b ∧
      (takenBy .a tr).Nodup ∧ (takenBy .b tr).Nodup :=
  Reflect.merged_once

-- The same for any walk, from any state: a taking needs its crossing not yet
-- moved on from `offered`.
example : ∀ {m last : Mix} {a b : List Note} {tr : List (Side × Note)} {evs : List Event},
    Walk m a b tr evs last → ∀ (s : Side),
    (takenBy s tr).Nodup ∧ ∀ k ∈ takenBy s tr, m.Fresh s.other k :=
  fun h => Reflect.Walk.once h

#print axioms Reflect.accepted_network
#print axioms Reflect.combine_merged
#print axioms Reflect.merged_exact
#print axioms Reflect.merged_once
#print axioms Reflect.Walk.once
