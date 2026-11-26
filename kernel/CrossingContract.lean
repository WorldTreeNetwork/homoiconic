import Reflect

open Reflect

-- Acceptance check for `add-recorded-crossing`. It fails to compile until the
-- theorems exist with exactly these signatures, for every table of
-- operations. This file does not import a table.

-- A record the check accepts is a run of the one-machine network: the
-- schedule the two guests' logs make is one the table allows, and it leads
-- the program, by direct evaluation, to a configuration whose compiled form
-- is the one the check reports. So every channel theorem holds of it. Since
-- `harden-crossing` this is for every turn space `cells` the two guests
-- agreed on, not only `turnSpace`.
example : ∀ [Ops] {cells budget : Nat} {p : Term} {a b : List Note} {evs : List Event} {cfg : MConfig},
    accept cells budget p a b = some (evs, cfg) →
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

-- `harden-crossing`: the check replays in the order the merge placed the
-- entries; that order is a walk the table allows, and its events are the
-- schedule `combine` gives.
example : ∀ {a b : List Note} {t : List (Side × Note × List Event)} {last : Mix},
    combineTrace a b = some (t, last) →
    Walk Mix.first a b (traceEntries t) (traceEvents t) last ∧ combine a b = some (traceEvents t) :=
  Reflect.combineTrace_walk

-- The check's replay, which charges each entry as its guest did, is
-- `schedIn` on that schedule when it runs every event: so `accepted_network`
-- speaks of what the check ran.
example : ∀ [Ops] (cells budget : Nat) (places : Side → List Nat) (t : List (Side × Note × List Event))
    (cfg : MConfig) (pa pb : Nat),
    (traceRun cells budget places cfg pa pb t).stopped = .ran →
    schedIn cells budget cfg (traceEvents t) =
      ((traceRun cells budget places cfg pa pb t).events,
        (traceRun cells budget places cfg pa pb t).cfg, .ran) :=
  Reflect.traceRun_sched

-- The measured runs are the runs: what a guest and the check charge is
-- measured on the very runs `schedIn` makes.
example : ∀ [Ops] (cells budget : Nat) (s : State),
    (runTurnMade cells budget s).1 = runTurnIn cells budget s := Reflect.runTurnMade_fst
example : ∀ [Ops] (cells budget : Nat) (c : MValue) (a : Data),
    (turnMade cells budget c a).1 = turnIn cells budget c a := Reflect.turnMade_fst
example : ∀ [Ops] (cells budget : Nat) (p : Term),
    (beginMade cells budget p).1 = beginIn cells budget p := Reflect.beginMade_fst
example : ∀ [Ops] (cells budget : Nat) (cfg : MConfig) (ev : Event),
    (stepMade cells budget cfg ev).1 = stepIn cells budget cfg ev := Reflect.stepMade_fst

-- The ledger walk. Between the start, or a count, and the next count, the
-- entries but the last charged no more than the credit the stretch began
-- with.
example : ∀ (hold : Nat) (seg rest : List Charged) (k credit : Nat) (r : Option (Nat × Nat)),
    holdGo hold k credit false false (seg ++ rest) = .ok r →
    (∀ e ∈ seg, e.note.isCount = false) →
    ((seg.dropLast).map (·.cost)).sum ≤ credit :=
  Reflect.hold_stretch

-- A count the walk goes on from is at most the bar, and the next stretch has
-- the hold less the count.
example : ∀ {hold k credit : Nat} {must cap : Bool} {r : Option (Nat × Nat)}
    {pre rest : List Charged} {m c ps : Nat},
    holdGo hold k credit must cap (pre ++ ⟨.held m, c, ps⟩ :: rest) = .ok r →
    m ≤ holdBar hold ∧ ∃ k' r', holdGo hold k' (hold - m) false false rest = .ok r' :=
  Reflect.hold_count

-- After `full` come only acknowledgements, at most `outLimit`.
example : ∀ {hold k credit : Nat} {must cap : Bool} {r : Option (Nat × Nat)}
    {pre rest : List Charged} {m c ps : Nat},
    holdGo hold k credit must cap (pre ++ ⟨.full m, c, ps⟩ :: rest) = .ok r →
    (∀ e ∈ rest, e.note.isAck = true) ∧ rest.length ≤ outLimit :=
  Reflect.hold_full

-- A side the walk accepts has a bounded number of entries.
example : ∀ {hold first : Nat} {es : List Charged} {r : Option (Nat × Nat)},
    holdWalk hold first es = .ok r → es.length ≤ entryLimit + outLimit + 2 :=
  Reflect.hold_entries

-- The greedy walk is complete (`homoiconic-q59.68`): two logs that have any
-- schedule the table allows combine. So `combine` refuses a pair of logs only
-- when no order of their entries is allowed.
example : ∀ {a b : List Note} {evs : List Event}, Merged a b evs → ∃ evs', combine a b = some evs' :=
  Reflect.combine_complete

-- A guest's log read alone (`homoiconic-q59.68`). `SideRun cells budget s L rs F`
-- reads the log `rs` of guest `s` from `L` to `F`, each entry with the packet
-- it took when it took one: what the entry needs of that guest's own
-- processes, and what it does to them with the machine's runs. Take two logs
-- that are each such a run from their guest's first state, with every crossing
-- taken as the packet its guest made for it. If they combine, the check
-- accepts them with the budgets they were run with, and what the replay
-- reaches is, at each guest's places and in order, that guest's processes. The
-- proof (`Walk.replay`) is for any order the table allows, not only the one
-- the walk chooses.
example : ∀ [Ops] {cells budget : Nat} {p : Term} {c₀ : MConfig} {ra rb : List (Note × Data)}
    {FA FB : Local} {t : List (Side × Note × List Event)} {last : Mix},
    beginIn cells budget p = some c₀ →
    SideRun cells budget .a (Local.init c₀.procs) ra FA →
    SideRun cells budget .b (Local.init []) rb FB →
    (∀ r ∈ ra, ∀ k, r.1.taking = some k → FB.outPkts[k]? = some r.2) →
    (∀ r ∈ rb, ∀ k, r.1.taking = some k → FA.outPkts[k]? = some r.2) →
    combineTrace (ra.map (·.1)) (rb.map (·.1)) = some (t, last) →
    ∃ cfg, accept cells budget p (ra.map (·.1)) (rb.map (·.1)) = some (traceEvents t, cfg) ∧
      last.placeA.filterMap (cfg.procs[·]?) = FA.procs ∧
      last.placeB.filterMap (cfg.procs[·]?) = FB.procs :=
  fun hb runA runB linkA linkB ht => Reflect.replay_agrees hb runA runB linkA linkB ht

#print axioms Reflect.accepted_network
#print axioms Reflect.combine_complete
#print axioms Reflect.replay_agrees
#print axioms Reflect.combine_merged
#print axioms Reflect.merged_exact
#print axioms Reflect.merged_once
#print axioms Reflect.Walk.once
#print axioms Reflect.combineTrace_walk
#print axioms Reflect.traceRun_sched
#print axioms Reflect.runTurnMade_fst
#print axioms Reflect.turnMade_fst
#print axioms Reflect.beginMade_fst
#print axioms Reflect.stepMade_fst
#print axioms Reflect.hold_stretch
#print axioms Reflect.hold_count
#print axioms Reflect.hold_full
#print axioms Reflect.hold_entries

-- The measured run runs as `runSpaceLeftWithin`, which caps the charge of a
-- step by the fuel (homoiconic-q59.81), proved the same function.
example : @runSpaceLeft = @runSpaceLeftWithin := Reflect.runSpaceLeft_eq_within
#print axioms Reflect.runSpaceLeft_eq_within
