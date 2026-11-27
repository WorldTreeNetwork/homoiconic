import Surface

open Reflect Surface.Cross

-- Acceptance check for `homoiconic-q59.68`: what two guests that follow the
-- protocol produce. It fails to compile until the theorems exist with exactly
-- these signatures. The guests are `Surface.Cross.Guest`, with the table the
-- image runs.
--
-- `Reach s` (`Surface/CrossModel.lean`): the pair `s` is reached from two
-- guests just started, each state changed only by the functions the image
-- calls: a step of `Guest.work` with any count of the cells held, the rest
-- `work` takes when no step is possible, `Guest.give`, `Guest.batch`, and
-- `Guest.take` of a batch the other guest made at some earlier time. Nothing
-- else is assumed of delivery: a batch may be lost, taken twice, or taken
-- after a later one. A batch is taken as the data it was made from; that its
-- bytes read back as that data is tested (P4), not proved.
--
-- `s.Quiet`: nothing is in flight. Neither guest keeps a packet the other has
-- not counted, and neither has accepted a packet it has not worked. Three of
-- the theorems below ask for it, and mid-run they do not hold: a crossing
-- taken whose acknowledgement is not yet worked leaves two logs that do not
-- combine (`CrossCheck.lean`, "mid-run"). That two guests that have closed
-- are quiet is not proved here. It rests on batches being answered one
-- exchange at a time and on a closed guest taking no further step
-- (`homoiconic-q59.85`); `CrossCheck.lean` asserts it of pairs it runs.

-- Where nothing is in flight, the two logs combine.
example : ∀ {s : Pair}, Reach s → s.Quiet →
    ∃ t last, combineTrace s.a.log.reverse s.b.log.reverse = some (t, last) :=
  fun h hq => Surface.Cross.honest_combine h hq

-- And once `a` has begun the program it was given (`c₀` is where it begins),
-- `accept` (the merge and the replay) accepts them with the budgets `a` ran
-- with. The check's own replay, `traceRun` from `c₀`, runs to the end too, to
-- the same configuration. What the replay reaches is, at each guest's places,
-- the processes that guest holds: as many places as processes, and the same
-- processes in order. So where `Surface.Cross.checkedAll` gets as far as its
-- replay, the lines it makes for a side (`procLines` of the replay at that
-- side's places) are the lines of what the guest holds, as many as the
-- places. The ledger walk, the reading of a record's text and the check's
-- own ceilings are not in this.
example : ∀ {s : Pair} {t : Term}, Reach s → s.Quiet → s.prog = some t → s.a.waiting = false →
    ∃ tr last c₀ cfg,
      combineTrace s.a.log.reverse s.b.log.reverse = some (tr, last) ∧
      beginIn s.a.cells s.a.budget t = some c₀ ∧
      accept s.a.cells s.a.budget t s.a.log.reverse s.b.log.reverse = some (traceEvents tr, cfg) ∧
      (∀ (places : Side → List Nat) (pa pb : Nat),
        (traceRun s.a.cells s.a.budget places c₀ pa pb tr).stopped = .ran ∧
        (traceRun s.a.cells s.a.budget places c₀ pa pb tr).cfg = cfg) ∧
      last.placeA.length = s.a.cfg.procs.length ∧ last.placeB.length = s.b.cfg.procs.length ∧
      last.placeA.filterMap (cfg.procs[·]?) = s.a.cfg.procs ∧
      last.placeB.filterMap (cfg.procs[·]?) = s.b.cfg.procs :=
  fun h hq hp hb => Surface.Cross.honest_accept h hq hp hb

-- A guest that has run anything runs with the other guest's step budget and
-- turn space, in every state reached. (A `b` that has run nothing may still
-- hold a budget above `a`'s.)
example : ∀ {s : Pair}, Reach s → s.b.fixed = true →
    s.b.budget = s.a.budget ∧ s.b.cells = s.a.cells :=
  fun h hf => Surface.Cross.honest_budget h hf

-- Where nothing is in flight, each guest's acknowledgements are in the order
-- the other took its crossings: the comparison the check makes.
example : ∀ {s : Pair}, Reach s → s.Quiet →
    acksOf s.b.log.reverse = takingsOf s.a.log.reverse ∧
    acksOf s.a.log.reverse = takingsOf s.b.log.reverse :=
  fun h hq => Surface.Cross.honest_acks h hq

-- What holds of every state reached, of which the four above are read off:
-- before `a` begins neither guest has done anything; after, each guest is
-- what its own log says, each packet worked is one the other made, in order
-- and once, and the entries in the order they were recorded are a path the
-- table allows.
example : ∀ {s : Pair}, Reach s → InvV s.a.view s.b.view s.toA s.toB s.prog :=
  fun h => Surface.Cross.Reach.inv h

-- The pair `CrossCheck.lean` runs in one process (`simulateWith`: `work`,
-- `batch` and `take` in turn, on bytes) is a pair the model reaches, with the
-- program the bytes read as, when a batch's bytes read back as the batch
-- (`ReadsBack`). That is P4, tested and not proved, so it is a hypothesis
-- here. The caller is the model's `b`. The image's exchanges are Zig and no
-- theorem speaks of them.
example : ReadsBack → ∀ (program : ByteArray) (u : Setup),
    ∃ s, Reach s ∧ (s.b, s.a) = simulateWith program u ∧
      s.prog = (Wire.readProgram program).toOption :=
  fun hread program u => Surface.Cross.Reach.simulate hread program u

#print axioms Surface.Cross.honest_combine
#print axioms Surface.Cross.Reach.simulate
#print axioms Surface.Cross.honest_accept
#print axioms Surface.Cross.honest_budget
#print axioms Surface.Cross.honest_acks
#print axioms Surface.Cross.Reach.inv
