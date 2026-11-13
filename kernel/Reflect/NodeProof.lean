import Reflect.Node
import Reflect.LogProof

/-!
What is proved about a node.

* A program and a log lead to at most one node (`node_deterministic`), and the
  node after a log is the node after a first part carried on through the rest
  (`node_prefix`).
* An op already in the log changes nothing (`node_again`, `node_redeliver`),
  and a node reached by a first part of the log, given the whole log, reaches
  what the whole log reaches (`node_restart`).
* A node's processes are where the schedule of first deliveries leads
  (`node_network`), so every channel theorem holds of them.
* The machine applies a log as direct evaluation does (`node_machine`,
  `node_machine_exact`), and what the executable `nodeRun` reports is true
  (`node_true`).
* An event is the runs of its plan and the configuration the plan then gives
  (`plan_step`, `step_plan`).
-/
namespace Reflect

section Generic
variable {C R C₁ R₁ C₂ R₂ : Type}

theorem Apply.deterministic {S : PSys C R} (hS : S.Det) {n a b : Node C R} {o : Op}
    (ha : Apply S n o a) (hb : Apply S n o b) : a = b := by
  cases ha with
  | repeated h =>
    cases hb with
    | repeated _ => rfl
    | happen h' _ => exact absurd h h'
  | happen h hs =>
    cases hb with
    | repeated h' => exact absurd h' h
    | happen _ hs' => rw [Step.deterministic hS hs hs']

theorem Applied.deterministic {S : PSys C R} (hS : S.Det) {n a b : Node C R} {ops : List Op}
    (ha : Applied S n ops a) (hb : Applied S n ops b) : a = b := by
  induction ha with
  | nil => cases hb; rfl
  | cons h _ ih =>
    cases hb with
    | cons h' rest' =>
      cases Apply.deterministic hS h h'
      exact ih rest'

theorem Begin.deterministic {S : PSys C R} (hS : S.Det) {p : Term} {a b : Config C R}
    (ha : Begin S p a) (hb : Begin S p b) : a = b := by
  obtain ⟨r, st, hr, hs, rfl⟩ := ha
  obtain ⟨r', st', hr', hs', rfl⟩ := hb
  cases hS.start hr hr'
  cases Settle.deterministic hS.toDet hs hs'
  rfl

theorem Ran.deterministic {S : PSys C R} (hS : S.Det) {p : Term} {ops : List Op}
    {a b : Node C R} (ha : Ran S p ops a) (hb : Ran S p ops b) : a = b := by
  obtain ⟨c, hc, hr⟩ := ha
  obtain ⟨c', hc', hr'⟩ := hb
  cases Begin.deterministic hS hc hc'
  exact Applied.deterministic hS hr hr'

theorem Applied.append {S : PSys C R} {n n'' : Node C R} {l₁ l₂ : List Op} :
    Applied S n (l₁ ++ l₂) n'' ↔ ∃ n', Applied S n l₁ n' ∧ Applied S n' l₂ n'' := by
  induction l₁ generalizing n with
  | nil => exact ⟨fun h => ⟨n, .nil, h⟩, fun ⟨_, h₁, h₂⟩ => by cases h₁; exact h₂⟩
  | cons o os ih =>
    rw [List.cons_append]
    constructor
    · intro h
      cases h with
      | cons hh rest =>
        obtain ⟨n', h₁, h₂⟩ := ih.mp rest
        exact ⟨n', .cons hh h₁, h₂⟩
    · intro ⟨n', h₁, h₂⟩
      cases h₁ with
      | cons hh rest => exact .cons hh (ih.mpr ⟨n', rest, h₂⟩)

theorem Ran.append {S : PSys C R} {p : Term} {l₁ l₂ : List Op} {n : Node C R} :
    Ran S p (l₁ ++ l₂) n ↔ ∃ s, Ran S p l₁ s ∧ Applied S s l₂ n := by
  constructor
  · intro ⟨c, hb, hr⟩
    obtain ⟨s, h₁, h₂⟩ := Applied.append.mp hr
    exact ⟨s, ⟨c, hb, h₁⟩, h₂⟩
  · intro ⟨s, ⟨c, hb, h₁⟩, h₂⟩
    exact ⟨c, hb, Applied.append.mpr ⟨s, h₁, h₂⟩⟩

theorem Apply.seen_iff {S : PSys C R} {n n' : Node C R} {o : Op} (hi : o.id ∈ n.seen) :
    Apply S n o n' ↔ n' = n := by
  constructor
  · intro h
    cases h with
    | repeated _ => rfl
    | happen h _ => exact absurd hi h
  · intro h
    subst h
    exact .repeated hi

theorem Apply.keeps {S : PSys C R} {n n' : Node C R} {o : Op} {x : Data}
    (h : Apply S n o n') (hi : x ∈ n.seen) : x ∈ n'.seen := by
  cases h with
  | repeated _ => exact hi
  | happen _ _ => exact List.mem_cons_of_mem _ hi

theorem Apply.takes {S : PSys C R} {n n' : Node C R} {o : Op} (h : Apply S n o n') :
    o.id ∈ n'.seen := by
  cases h with
  | repeated h => exact h
  | happen _ _ => exact List.mem_cons_self

theorem Applied.keeps {S : PSys C R} {n n' : Node C R} {ops : List Op} {x : Data}
    (h : Applied S n ops n') (hi : x ∈ n.seen) : x ∈ n'.seen := by
  induction h with
  | nil => exact hi
  | cons hh _ ih => exact ih (hh.keeps hi)

/-- After a log, the node has acted on the identifier of each of its ops. -/
theorem Applied.takes {S : PSys C R} {n n' : Node C R} {ops : List Op} {o : Op}
    (h : Applied S n ops n') (hm : o ∈ ops) : o.id ∈ n'.seen := by
  induction h with
  | nil => cases hm
  | cons hh rest ih =>
    rcases List.mem_cons.mp hm with he | he
    · subst he; exact rest.keeps hh.takes
    · exact ih he

theorem Applied.seen_all {S : PSys C R} {n n' : Node C R} {ops : List Op}
    (hall : ∀ o, o ∈ ops → o.id ∈ n.seen) : Applied S n ops n' ↔ n' = n := by
  induction ops with
  | nil => exact ⟨fun h => by cases h; rfl, fun h => by subst h; exact .nil⟩
  | cons o os ih =>
    have ho := hall o List.mem_cons_self
    have hos : ∀ x, x ∈ os → x.id ∈ n.seen := fun x hx => hall x (List.mem_cons_of_mem _ hx)
    constructor
    · intro h
      cases h with
      | cons hh rest =>
        cases (Apply.seen_iff ho).mp hh
        exact (ih hos).mp rest
    · intro h
      subst h
      exact .cons ((Apply.seen_iff ho).mpr rfl) ((ih hos).mpr rfl)

theorem Applied.again {S : PSys C R} {n n' n'' : Node C R} {ops : List Op} {o : Op}
    (h : Applied S n ops n') (hm : o ∈ ops) : Apply S n' o n'' ↔ n'' = n' :=
  Apply.seen_iff (h.takes hm)

theorem Applied.redeliver {S : PSys C R} {n n' : Node C R} {l₁ l₂ : List Op} {o : Op}
    (hm : o ∈ l₁) : Applied S n (l₁ ++ o :: l₂) n' ↔ Applied S n (l₁ ++ l₂) n' := by
  rw [Applied.append, Applied.append]
  constructor
  · intro ⟨m, h₁, h₂⟩
    cases h₂ with
    | cons hh rest =>
      cases (h₁.again hm).mp hh
      exact ⟨m, h₁, rest⟩
  · intro ⟨m, h₁, h₂⟩
    exact ⟨m, h₁, .cons ((h₁.again hm).mpr rfl) h₂⟩

theorem Applied.restart {S : PSys C R} {n s t : Node C R} {l₁ l₂ : List Op}
    (h : Applied S n l₁ s) : Applied S s (l₁ ++ l₂) t ↔ Applied S s l₂ t := by
  have ign : ∀ m, Applied S s l₁ m ↔ m = s := fun _ => Applied.seen_all (fun _ ho => h.takes ho)
  rw [Applied.append]
  constructor
  · intro ⟨m, h₁, h₂⟩
    cases (ign m).mp h₁
    exact h₂
  · intro h₂
    exact ⟨s, (ign s).mpr rfl, h₂⟩

/-- A log applied to a node moves its processes through the schedule of the
    log's first deliveries. -/
theorem Applied.sched {S : PSys C R} {ops : List Op} : ∀ {c : Config C R} {seen : List Data}
    {n' : Node C R}, Applied S ⟨c, seen⟩ ops n' →
    Sched S c ((firstOps seen ops).map (·.event)) n'.cfg := by
  induction ops with
  | nil => intro c seen n' h; cases h; exact .nil
  | cons o os ih =>
    intro c seen n' h
    cases h with
    | cons hh rest =>
      by_cases hm : o.id ∈ seen
      · have hf : firstOps seen (o :: os) = firstOps seen os := by simp [firstOps, hm]
        rw [hf]
        cases (Apply.seen_iff (n := ⟨c, seen⟩) hm).mp hh
        exact ih rest
      · have hf : firstOps seen (o :: os) = o :: firstOps (o.id :: seen) os := by
          simp [firstOps, hm]
        rw [hf]
        cases hh with
        | repeated h' => exact absurd h' hm
        | happen _ hs => exact .cons hs (ih rest)

theorem Ran.network {S : PSys C R} {p : Term} {ops : List Op} {n : Node C R}
    (h : Ran S p ops n) : Network S p ((firstOps [] ops).map (·.event)) n.cfg := by
  obtain ⟨c, hb, hr⟩ := h
  exact ⟨c, hb, hr.sched⟩

theorem PSim.apply_forward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {n n' : Node C₁ R₁} {o : Op} (h : Apply S₁ n o n') :
    Apply S₂ (n.map f g) o (n'.map f g) := by
  cases h with
  | repeated h => exact .repeated h
  | happen h hs => exact .happen h (s.step_forward hs)

theorem PSim.apply_backward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {n : Node C₁ R₁} {w : Node C₂ R₂} {o : Op}
    (h : Apply S₂ (n.map f g) o w) : ∃ n', Apply S₁ n o n' ∧ w = n'.map f g := by
  generalize hn : n.map f g = mn at h
  cases h with
  | repeated h => subst hn; exact ⟨n, .repeated h, rfl⟩
  | happen h hs =>
    subst hn
    obtain ⟨cfg₁, hs₁, rfl⟩ := s.step_backward hs
    exact ⟨⟨cfg₁, o.id :: n.seen⟩, .happen h hs₁, rfl⟩

theorem PSim.applied_forward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {n n' : Node C₁ R₁} {ops : List Op} (h : Applied S₁ n ops n') :
    Applied S₂ (n.map f g) ops (n'.map f g) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (s.apply_forward h) ih

theorem PSim.applied_backward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {w w' : Node C₂ R₂} {ops : List Op} (h : Applied S₂ w ops w') :
    ∀ n : Node C₁ R₁, w = n.map f g → ∃ n', Applied S₁ n ops n' ∧ w' = n'.map f g := by
  induction h with
  | nil => intro n hn; exact ⟨n, .nil, hn⟩
  | cons h _ ih =>
    intro n hn
    subst hn
    obtain ⟨mid, hm, rfl⟩ := s.apply_backward h
    obtain ⟨n', hr, he⟩ := ih mid rfl
    exact ⟨n', .cons hm hr, he⟩

theorem PSim.ran_forward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {p : Term} {ops : List Op} {n : Node C₁ R₁}
    (h : Ran S₁ p ops n) : Ran S₂ p ops (n.map f g) := by
  obtain ⟨c, ⟨r, st, hr, hs, rfl⟩, hd⟩ := h
  exact ⟨Config.map f g ⟨[⟨st, []⟩], []⟩,
    ⟨f r, st.map f g, (s.start _ _).mpr ⟨_, hr, rfl⟩, s.sim.settle_forward hs, rfl⟩,
    s.applied_forward hd⟩

theorem PSim.ran_backward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {p : Term} {ops : List Op} {w : Node C₂ R₂}
    (h : Ran S₂ p ops w) : ∃ n, Ran S₁ p ops n ∧ w = n.map f g := by
  obtain ⟨c, ⟨r₂, st₂, hr, hs, rfl⟩, hd⟩ := h
  obtain ⟨r₁, hr₁, rfl⟩ := (s.start _ _).mp hr
  obtain ⟨st₁, hs₁, rfl⟩ := s.sim.settle_backward hs
  obtain ⟨n, hd₁, he⟩ := s.applied_backward hd ⟨⟨[⟨st₁, []⟩], []⟩, []⟩ rfl
  exact ⟨n, ⟨_, ⟨r₁, st₁, hr₁, hs₁, rfl⟩, hd₁⟩, he⟩

/-- An event that a plan's runs and its configuration make up is the event. -/
theorem plan_step {S : PSys C R} {cfg cfg' : Config C R} {ev : Event} {jobs : List (Job C)}
    {done : List (Status C R) → Option (Config C R)} {sts : List (Status C R)}
    (hp : plan cfg ev = some (jobs, done)) (hr : Job.AllRun S jobs sts)
    (hd : done sts = some cfg') : Step S cfg ev cfg' := by
  cases ev with
  | fresh i n =>
    simp only [plan] at hp
    split at hp
    · next c p held hi =>
      split at hp
      · next hq =>
        split at hp
        · cases hp
        · next hn =>
          cases hp
          match sts, hr, hd with
          | [st], ⟨h₁, _⟩, hd =>
            cases hd
            exact .fresh hi hq hn h₁
      · cases hp
    · cases hp
  | spawn i =>
    simp only [plan] at hp
    split at hp
    · next c p held hi =>
      split at hp
      · next t arg hq =>
        cases hp
        match sts, hr, hd with
        | [child, st], ⟨⟨r, hs, hc⟩, h₂, _⟩, hd =>
          cases hd
          exact .spawn hi hq hs hc h₂
      · cases hp
    · cases hp
  | comm i j =>
    simp only [plan] at hp
    split at hp
    · next c p held c' p' held' hi hj =>
      split at hp
      · next ch v ch' hq hq' =>
        split at hp
        · next hc =>
          obtain ⟨rfl, hh, hh'⟩ := hc
          cases hp
          match sts, hr, hd with
          | [st, st'], ⟨h₁, h₂, _⟩, hd =>
            cases hd
            exact .comm hi hj hq hq' hh hh' h₁ h₂
        · cases hp
      · cases hp
    · cases hp
  | answer i a =>
    simp only [plan] at hp
    split at hp
    · next c p held hi =>
      split at hp
      · next hq =>
        cases hp
        match sts, hr, hd with
        | [st], ⟨h₁, _⟩, hd =>
          cases hd
          exact .answer hi hq h₁
      · cases hp
    · cases hp

/-- Every event is the runs of its plan and the configuration the plan gives. -/
theorem step_plan {S : PSys C R} {cfg cfg' : Config C R} {ev : Event}
    (h : Step S cfg ev cfg') :
    ∃ jobs done sts, plan cfg ev = some (jobs, done) ∧
      Job.AllRun S jobs sts ∧ done sts = some cfg' := by
  cases h with
  | @fresh i n c p held st hi hq hn ht =>
    have hp : ∃ done, plan cfg (.fresh i n) = some ([.turn c (.nat n)], done) ∧
        done [st] = some ⟨cfg.procs.set i ⟨st, n :: held⟩, n :: cfg.names⟩ := by
      simp [plan, hi, hq, hn]
    obtain ⟨done, hp, hd⟩ := hp
    exact ⟨_, done, [st], hp, ⟨ht, trivial⟩, hd⟩
  | @spawn i c p held t arg r child st hi hq hs hc ht =>
    have hp : ∃ done, plan cfg (.spawn i) =
        some ([.start (.app t (.lit arg)), .turn c (.arr [])], done) ∧
        done [child, st] =
          some ⟨cfg.procs.set i ⟨st, held⟩ ++ [⟨child, grant held arg⟩], cfg.names⟩ := by
      simp [plan, hi, hq]
    obtain ⟨done, hp, hd⟩ := hp
    exact ⟨_, done, [child, st], hp, ⟨⟨r, hs, hc⟩, ht, trivial⟩, hd⟩
  | @comm i j c p held c' p' held' ch v st st' hi hj hq hq' hh hh' ht ht' =>
    have hp : ∃ done, plan cfg (.comm i j) = some ([.turn c (.arr []), .turn c' v], done) ∧
        done [st, st'] = some ⟨(cfg.procs.set i ⟨st, held⟩).set j
          ⟨st', grant held v ++ held'⟩, cfg.names⟩ := by
      simp [plan, hi, hj, hq, hq', hh, hh']
    obtain ⟨done, hp, hd⟩ := hp
    exact ⟨_, done, [st, st'], hp, ⟨ht, ht', trivial⟩, hd⟩
  | @answer i a c p held st hi hq ht =>
    have hp : ∃ done, plan cfg (.answer i a) = some ([.turn c a], done) ∧
        done [st] = some ⟨cfg.procs.set i ⟨st, held⟩, cfg.names⟩ := by
      simp [plan, hi, hq]
    obtain ⟨done, hp, hd⟩ := hp
    exact ⟨_, done, [st], hp, ⟨ht, trivial⟩, hd⟩

end Generic

variable [Ops]
open MP

/-- The node a program reaches is a function of the program and the log. -/
theorem node_deterministic {p : Term} {ops : List Op} {a b : Node Value Outcome}
    (ha : Ran sourceP p ops a) (hb : Ran sourceP p ops b) : a = b :=
  Ran.deterministic sourceP_det ha hb

theorem node_prefix {p : Term} {l₁ l₂ : List Op} {n : Node Value Outcome} :
    Ran sourceP p (l₁ ++ l₂) n ↔ ∃ s, Ran sourceP p l₁ s ∧ Applied sourceP s l₂ n :=
  Ran.append

/-- Applying an op that is already in the log leaves the node as it is. -/
theorem node_again {p : Term} {ops : List Op} {n n' : Node Value Outcome} {o : Op}
    (h : Ran sourceP p ops n) (hm : o ∈ ops) : Apply sourceP n o n' ↔ n' = n := by
  obtain ⟨_, _, hr⟩ := h
  exact hr.again hm

theorem node_redeliver {p : Term} {l₁ l₂ : List Op} {o : Op} {n : Node Value Outcome}
    (hm : o ∈ l₁) : Ran sourceP p (l₁ ++ o :: l₂) n ↔ Ran sourceP p (l₁ ++ l₂) n := by
  constructor
  · intro ⟨c, hb, hr⟩; exact ⟨c, hb, (Applied.redeliver hm).mp hr⟩
  · intro ⟨c, hb, hr⟩; exact ⟨c, hb, (Applied.redeliver hm).mpr hr⟩

/-- A node reached by a first part of the log, given the whole log, reaches
    what the whole log reaches from the start. -/
theorem node_restart {p : Term} {l₁ l₂ : List Op} {s n : Node Value Outcome}
    (h : Ran sourceP p l₁ s) :
    Applied sourceP s (l₁ ++ l₂) n ↔ Ran sourceP p (l₁ ++ l₂) n := by
  obtain ⟨c, hb, hr⟩ := h
  refine (hr.restart (l₂ := l₂) (t := n)).trans ?_
  constructor
  · intro h₂; exact Ran.append.mpr ⟨s, ⟨c, hb, hr⟩, h₂⟩
  · intro hl
    obtain ⟨s', hs', h₂⟩ := Ran.append.mp hl
    cases Ran.deterministic sourceP_det hs' ⟨c, hb, hr⟩
    exact h₂

/-- A node's processes are where the schedule of the log's first deliveries
    leads the program. -/
theorem node_network {p : Term} {ops : List Op} {n : Node Value Outcome}
    (h : Ran sourceP p ops n) :
    Network sourceP p ((firstOps [] ops).map (·.event)) n.cfg :=
  h.network

theorem node_machine {p : Term} {ops : List Op} {n : Node Value Outcome}
    (h : Ran sourceP p ops n) : Ran machineP p ops (n.map MP.injO injV) :=
  psim_machine.ran_forward h

theorem node_machine_exact {p : Term} {ops : List Op} {w : MNode}
    (h : Ran machineP p ops w) : ∃ n, Ran sourceP p ops n ∧ w = n.map MP.injO injV :=
  psim_machine.ran_backward h

theorem nodeRun_sound {budget : Nat} : ∀ (ops : List Op) (n : MNode),
    Applied machineP n (nodeRun budget n ops).1 (nodeRun budget n ops).2.1 := by
  intro ops
  induction ops with
  | nil => intro n; exact .nil
  | cons o os ih =>
    intro n
    rw [nodeRun]
    split
    · next hm => exact .cons (.repeated hm) (ih n)
    · next hm =>
      split
      · next cfg' hs => exact .cons (.happen hm (stepRun_sound hs)) (ih _)
      · exact .nil
      · exact .nil

/-- What the executable node reports after a log is true of the program,
    however the run stopped: the ops it reports as applied are a log of the
    program by direct evaluation, and the node it reports is the compiled form
    of where that log leads. -/
theorem node_true {budget : Nat} {p : Term} {c₀ : MConfig} (ops : List Op)
    (h : beginRun budget p = some c₀) :
    ∃ n, Ran sourceP p (nodeRun budget ⟨c₀, []⟩ ops).1 n ∧
      (nodeRun budget ⟨c₀, []⟩ ops).2.1 = n.map MP.injO injV :=
  node_machine_exact ⟨c₀, beginRun_sound h, nodeRun_sound ops _⟩

end Reflect
