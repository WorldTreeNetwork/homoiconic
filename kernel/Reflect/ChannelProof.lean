import Reflect.Channel
import Reflect.RequestProof

/-!
What is proved about channels.

- `Step.deterministic`, `Sched.deterministic`: where a schedule leads is fixed
  by where it starts and the schedule. The names made and the answers from
  outside are part of the schedule.
- `Step.comm_held`: a send and a receive meet only on a name both hold.
- `Step.held_from`: a process holds a name after an event only if it held it
  before, or the event made it for that process, or the event is a message or a
  start from a process that held it.
- `Sched.held_issued`: every name held was made by an event of the schedule.
- `Network.held_nodup`: no process of a program holds a name twice.
- `PSim.forward`, `PSim.backward`: a run by direct evaluation is, in compiled
  form, a run on the machine, and the machine has no others.
- `network_reflective`: the interpreter on data runs a schedule as the program
  does, each evaluation done by `interp` on the data form.
- `stepRun_sound`, `schedRun_sound`, `autoRun_sound`: the executable scheduler
  only does what `Step` says.
-/
namespace Reflect

section Lists
variable {α β : Type}

theorem getElem?_set_cases {l : List α} {i k : Nat} {a q : α}
    (h : (l.set i a)[k]? = some q) : (i = k ∧ q = a) ∨ (i ≠ k ∧ l[k]? = some q) := by
  rw [List.getElem?_set] at h
  split at h
  · next hik =>
    split at h
    · cases h; exact .inl ⟨hik, rfl⟩
    · cases h
  · next hik => exact .inr ⟨hik, h⟩

theorem getElem?_append_single {l : List α} {x q : α} {k : Nat}
    (h : (l ++ [x])[k]? = some q) : l[k]? = some q ∨ q = x := by
  rw [List.getElem?_append] at h
  split at h
  · exact .inl h
  · match hm : k - l.length with
    | 0 => rw [hm] at h; simp at h; exact .inr h.symm
    | m + 1 => rw [hm] at h; simp at h

end Lists

section Generic
variable {C R C₁ R₁ C₂ R₂ : Type}

/-- What determinism of a schedule needs from a way of evaluating. -/
structure PSys.Det (S : PSys C R) : Prop where
  toDet : S.toSys.Det
  start : ∀ {t r r'}, S.start t r → S.start t r' → r = r'

theorem Settle.deterministic {S : Sys C R} (hS : S.Det) {r : R} {a b : Status C R}
    (h : Settle S r a) (h' : Settle S r b) : a = b := by
  cases h with
  | stop h =>
    cases h' with
    | stop _ => rfl
    | payloadFails h2 _ _ _ => rw [h] at h2; cases h2
    | payloadFunction h2 _ _ => rw [h] at h2; cases h2
    | wait h2 _ _ => rw [h] at h2; cases h2
  | payloadFails h hp hf hd =>
    cases h' with
    | stop h2 => rw [h] at h2; cases h2
    | payloadFails h2 hp2 _ _ => rw [h] at h2; cases h2; cases hS.eval hp hp2; rfl
    | payloadFunction h2 hp2 hf2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hf] at hf2; cases hf2
    | wait h2 hp2 hd2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hd] at hd2; cases hd2
  | payloadFunction h hp hf =>
    cases h' with
    | stop h2 => rw [h] at h2; cases h2
    | payloadFails h2 hp2 hf2 _ =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hf] at hf2; cases hf2
    | payloadFunction _ _ _ => rfl
    | wait h2 hp2 hd2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hS.excl hf] at hd2; cases hd2
  | wait h hp hd =>
    cases h' with
    | stop h2 => rw [h] at h2; cases h2
    | payloadFails h2 hp2 _ hd2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hd] at hd2; cases hd2
    | payloadFunction h2 hp2 hf2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hS.excl hf2] at hd; cases hd
    | wait h2 hp2 hd2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hd] at hd2; cases hd2; rfl

theorem Turn.deterministic {S : Sys C R} (hS : S.Det) {c : C} {x : Data} {a b : Status C R}
    (h : Turn S c x a) (h' : Turn S c x b) : a = b := by
  obtain ⟨r, hr, hs⟩ := h
  obtain ⟨r', hr', hs'⟩ := h'
  cases hS.eval hr hr'
  exact Settle.deterministic hS hs hs'

/-- An event leads to one configuration. -/
theorem Step.deterministic {S : PSys C R} (hS : S.Det) {cfg a b : Config C R} {ev : Event}
    (h : Step S cfg ev a) (h' : Step S cfg ev b) : a = b := by
  cases h with
  | fresh hi hq hn ht =>
    cases h' with
    | fresh hi2 hq2 hn2 ht2 =>
      rw [hi] at hi2; cases hi2
      cases Turn.deterministic hS.toDet ht ht2
      rfl
  | spawn hi hq hs hc ht =>
    cases h' with
    | spawn hi2 hq2 hs2 hc2 ht2 =>
      rw [hi] at hi2; cases hi2
      rw [hq] at hq2; cases hq2
      cases hS.start hs hs2
      cases Settle.deterministic hS.toDet hc hc2
      cases Turn.deterministic hS.toDet ht ht2
      rfl
  | comm hi hj hq hq' hh hh' ht ht' =>
    cases h' with
    | comm hi2 hj2 hq2 hq2' _ _ ht2 ht2' =>
      rw [hi] at hi2; cases hi2
      rw [hj] at hj2; cases hj2
      rw [hq] at hq2; cases hq2
      cases Turn.deterministic hS.toDet ht ht2
      cases Turn.deterministic hS.toDet ht' ht2'
      rfl
  | answer hi hq ht =>
    cases h' with
    | answer hi2 hq2 ht2 =>
      rw [hi] at hi2; cases hi2
      cases Turn.deterministic hS.toDet ht ht2
      rfl

/-- A schedule leads to one configuration. -/
theorem Sched.deterministic {S : PSys C R} (hS : S.Det) {cfg a b : Config C R}
    {evs : List Event} (h : Sched S cfg evs a) (h' : Sched S cfg evs b) : a = b := by
  induction h with
  | nil => cases h'; rfl
  | cons h _ ih =>
    cases h' with
    | cons h2 rest2 =>
      cases Step.deterministic hS h h2
      exact ih rest2

theorem Network.deterministic {S : PSys C R} (hS : S.Det) {p : Term} {evs : List Event}
    {a b : Config C R} (h : Network S p evs a) (h' : Network S p evs b) : a = b := by
  obtain ⟨c, ⟨r, st, hr, hs, rfl⟩, hd⟩ := h
  obtain ⟨c', ⟨r', st', hr', hs', rfl⟩, hd'⟩ := h'
  cases hS.start hr hr'
  cases Settle.deterministic hS.toDet hs hs'
  exact Sched.deterministic hS hd hd'

/-- A send and a receive meet only on a name both processes hold. -/
theorem Step.comm_held {S : PSys C R} {cfg cfg' : Config C R} {i j : Nat}
    (h : Step S cfg (.comm i j) cfg') :
    ∃ ch v c p held c' p' held',
      cfg.procs[i]? = some ⟨.waiting c p, held⟩ ∧ classify p = .send ch v ∧ ch ∈ held ∧
      cfg.procs[j]? = some ⟨.waiting c' p', held'⟩ ∧ classify p' = .receive ch ∧ ch ∈ held' := by
  cases h with
  | comm hi hj hq hq' hh hh' _ _ => exact ⟨_, _, _, _, _, _, _, _, hi, hq, hh, hj, hq', hh'⟩

/-- Where a held name comes from. After an event, process `k` holds `n` only
    if it held `n` before, or the event made `n` for it, or the event is a
    message to it, or a start, from a process that held `n`. -/
theorem Step.held_from {S : PSys C R} {cfg cfg' : Config C R} {ev : Event}
    (h : Step S cfg ev cfg') {k n : Nat} {q : Proc C R}
    (hk : cfg'.procs[k]? = some q) (hn : n ∈ q.held) :
    (∃ q₀, cfg.procs[k]? = some q₀ ∧ n ∈ q₀.held) ∨ ev = .fresh k n ∨
    (∃ i q₀, cfg.procs[i]? = some q₀ ∧ n ∈ q₀.held ∧ (ev = .comm i k ∨ ev = .spawn i)) := by
  cases h with
  | fresh hi hq hfresh ht =>
    rcases getElem?_set_cases hk with ⟨rfl, rfl⟩ | ⟨_, hk'⟩
    · rcases List.mem_cons.mp hn with rfl | hn'
      · exact .inr (.inl rfl)
      · exact .inl ⟨_, hi, hn'⟩
    · exact .inl ⟨_, hk', hn⟩
  | spawn hi hq hs hc ht =>
    rcases getElem?_append_single hk with hk' | rfl
    · rcases getElem?_set_cases hk' with ⟨rfl, rfl⟩ | ⟨_, hk''⟩
      · exact .inl ⟨_, hi, hn⟩
      · exact .inl ⟨_, hk'', hn⟩
    · exact .inr (.inr ⟨_, _, hi, (List.mem_filter.mp hn).1, .inr rfl⟩)
  | @comm i j c p held c' p' held' ch v st st' hi hj hq hq' hh hh' ht ht' =>
    rcases getElem?_set_cases hk with ⟨rfl, rfl⟩ | ⟨_, hk'⟩
    · have hn : n ∈ (grant held v).filter (fun n => !held'.contains n) ++ held' := hn
      rcases List.mem_append.mp hn with hg | hn'
      · exact .inr (.inr ⟨_, _, hi,
          (List.mem_filter.mp (List.mem_filter.mp hg).1).1, .inl rfl⟩)
      · exact .inl ⟨_, hj, hn'⟩
    · rcases getElem?_set_cases hk' with ⟨rfl, rfl⟩ | ⟨_, hk''⟩
      · exact .inl ⟨_, hi, hn⟩
      · exact .inl ⟨_, hk'', hn⟩
  | answer hi hq ht =>
    rcases getElem?_set_cases hk with ⟨rfl, rfl⟩ | ⟨_, hk'⟩
    · exact .inl ⟨_, hi, hn⟩
    · exact .inl ⟨_, hk', hn⟩

/-- Every name held after a schedule was held at its start or made by one of
    its events. -/
theorem Sched.held_issued {S : PSys C R} {c₀ cfg : Config C R} {evs : List Event}
    (h : Sched S c₀ evs cfg) : ∀ {k n : Nat} {q : Proc C R},
    cfg.procs[k]? = some q → n ∈ q.held →
    (∃ (i : Nat) (q₀ : Proc C R), c₀.procs[i]? = some q₀ ∧ n ∈ q₀.held) ∨
      ∃ i, Event.fresh i n ∈ evs := by
  induction h with
  | nil => intro k n q hk hn; exact .inl ⟨_, _, hk, hn⟩
  | cons h _ ih =>
    intro k n q hk hn
    rcases ih hk hn with ⟨i, q₀, hi, hn'⟩ | ⟨i, hi⟩
    · rcases h.held_from hi hn' with ⟨q₁, h1, h2⟩ | rfl | ⟨j, q₁, h1, h2, _⟩
      · exact .inl ⟨_, _, h1, h2⟩
      · exact .inr ⟨_, List.mem_cons_self⟩
      · exact .inl ⟨_, _, h1, h2⟩
    · exact .inr ⟨i, List.mem_cons_of_mem _ hi⟩

/-- A program run as the first process holds only names its schedule made. -/
theorem Network.held_issued {S : PSys C R} {p : Term} {evs : List Event} {cfg : Config C R}
    (h : Network S p evs cfg) {k n : Nat} {q : Proc C R}
    (hk : cfg.procs[k]? = some q) (hn : n ∈ q.held) : ∃ i, Event.fresh i n ∈ evs := by
  obtain ⟨c, ⟨r, st, _, _, rfl⟩, hd⟩ := h
  rcases hd.held_issued hk hn with ⟨i, q₀, hi, hn'⟩ | h'
  · cases i with
    | zero => simp at hi; subst hi; cases hn'
    | succ i => simp at hi
  · exact h'

/-- What is handed over, added to a list with no repeat, has no repeat. -/
theorem gain_nodup {held' handed : List Nat} (h' : held'.Nodup) (h : handed.Nodup) :
    (gain held' handed).Nodup := by
  unfold gain
  refine List.nodup_append.mpr ⟨h.sublist List.filter_sublist, h', ?_⟩
  intro a ha b hb hab
  subst hab
  have := (List.mem_filter.mp ha).2
  simp [hb] at this

/-- Every held list has no repeat and holds only names that were made. -/
def Config.Tidy (cfg : Config C R) : Prop :=
  ∀ (k : Nat) (q : Proc C R), cfg.procs[k]? = some q →
    q.held.Nodup ∧ ∀ n, n ∈ q.held → n ∈ cfg.names

theorem Step.tidy {S : PSys C R} {cfg cfg' : Config C R} {ev : Event}
    (h : Step S cfg ev cfg') (ht : cfg.Tidy) : cfg'.Tidy := by
  intro k q hk
  cases h with
  | fresh hi hq hfresh _ =>
    obtain ⟨hnd, hsub⟩ := ht _ _ hi
    rcases getElem?_set_cases hk with ⟨rfl, rfl⟩ | ⟨_, hk'⟩
    · refine ⟨List.nodup_cons.mpr ⟨fun hm => hfresh (hsub _ hm), hnd⟩, ?_⟩
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub _ hm')
    · exact ⟨(ht _ _ hk').1, fun m hm => List.mem_cons_of_mem _ ((ht _ _ hk').2 m hm)⟩
  | spawn hi hq hs hc _ =>
    obtain ⟨hnd, hsub⟩ := ht _ _ hi
    rcases getElem?_append_single hk with hk' | rfl
    · rcases getElem?_set_cases hk' with ⟨rfl, rfl⟩ | ⟨_, hk''⟩
      · exact ⟨hnd, hsub⟩
      · exact ht _ _ hk''
    · exact ⟨hnd.sublist List.filter_sublist, fun m hm => hsub m (List.mem_filter.mp hm).1⟩
  | @comm i j c p held c' p' held' ch v st st' hi hj hq hq' hh hh' _ _ =>
    obtain ⟨hnd, hsub⟩ := ht _ _ hi
    obtain ⟨hnd', hsub'⟩ := ht _ _ hj
    rcases getElem?_set_cases hk with ⟨rfl, rfl⟩ | ⟨_, hk'⟩
    · refine ⟨gain_nodup hnd' (hnd.sublist List.filter_sublist), ?_⟩
      intro m hm
      have hm : m ∈ (grant held v).filter (fun n => !held'.contains n) ++ held' := hm
      rcases List.mem_append.mp hm with hg | hm'
      · exact hsub m (List.mem_filter.mp (List.mem_filter.mp hg).1).1
      · exact hsub' m hm'
    · rcases getElem?_set_cases hk' with ⟨rfl, rfl⟩ | ⟨_, hk''⟩
      · exact ⟨hnd, hsub⟩
      · exact ht _ _ hk''
  | answer hi hq _ =>
    obtain ⟨hnd, hsub⟩ := ht _ _ hi
    rcases getElem?_set_cases hk with ⟨rfl, rfl⟩ | ⟨_, hk'⟩
    · exact ⟨hnd, hsub⟩
    · exact ht _ _ hk'

theorem Sched.tidy {S : PSys C R} {c₀ cfg : Config C R} {evs : List Event}
    (h : Sched S c₀ evs cfg) (ht : c₀.Tidy) : cfg.Tidy := by
  induction h with
  | nil => exact ht
  | cons h _ ih => exact ih (h.tidy ht)

/-- No process of a program holds a name twice. -/
theorem Network.held_nodup {S : PSys C R} {p : Term} {evs : List Event} {cfg : Config C R}
    (h : Network S p evs cfg) {k : Nat} {q : Proc C R}
    (hk : cfg.procs[k]? = some q) : q.held.Nodup := by
  obtain ⟨c, ⟨r, st, _, _, rfl⟩, hd⟩ := h
  refine (hd.tidy ?_ k q hk).1
  intro i q₀ hi
  cases i with
  | zero => simp at hi; subst hi; exact ⟨List.nodup_nil, fun _ hm => by cases hm⟩
  | succ i => simp at hi

/-- Two ways of evaluating that agree turn by turn and on beginning a program. -/
structure PSim (S₁ : PSys C₁ R₁) (S₂ : PSys C₂ R₂) (f : R₁ → R₂) (g : C₁ → C₂) : Prop where
  sim : Sim S₁.toSys S₂.toSys f g
  start : ∀ t r₂, S₂.start t r₂ ↔ ∃ r₁, S₁.start t r₁ ∧ r₂ = f r₁

theorem Sim.settle_backward {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {r : R₁} {st₂ : Status C₂ R₂} (h : Settle S₂ (f r) st₂) :
    ∃ st₁, Settle S₁ r st₁ ∧ st₂ = st₁.map f g := by
  generalize hr : f r = r₂ at h
  cases h with
  | stop h =>
    subst hr
    exact ⟨.finished r, .stop (s.fn_none h), rfl⟩
  | payloadFails h hp hf hd =>
    subst hr
    obtain ⟨c, hc, rfl⟩ := s.fn_some h
    obtain ⟨r₁, hp₁, rfl⟩ := (s.eval _ _ _).mp hp
    exact ⟨.finished r₁, .payloadFails hc hp₁ (s.fn_none hf) (by rw [← s.dat, hd]), rfl⟩
  | payloadFunction h hp hf =>
    subst hr
    obtain ⟨c, hc, rfl⟩ := s.fn_some h
    obtain ⟨r₁, hp₁, rfl⟩ := (s.eval _ _ _).mp hp
    obtain ⟨c', hc', _⟩ := s.fn_some hf
    exact ⟨.finished S₁.wrong, .payloadFunction hc hp₁ hc', by rw [← s.wrong]; rfl⟩
  | wait h hp hd =>
    subst hr
    obtain ⟨c, hc, rfl⟩ := s.fn_some h
    obtain ⟨r₁, hp₁, rfl⟩ := (s.eval _ _ _).mp hp
    exact ⟨.waiting c _, .wait hc hp₁ (by rw [← s.dat, hd]), rfl⟩

theorem Sim.turn_backward {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {c : C₁} {a : Data} {st₂ : Status C₂ R₂} (h : Turn S₂ (g c) a st₂) :
    ∃ st₁, Turn S₁ c a st₁ ∧ st₂ = st₁.map f g := by
  obtain ⟨r₂, hr, hs⟩ := h
  obtain ⟨r₁, hr₁, rfl⟩ := (s.eval _ _ _).mp hr
  obtain ⟨st₁, hs₁, he⟩ := s.settle_backward hs
  exact ⟨st₁, ⟨r₁, hr₁, hs₁⟩, he⟩

/-- A waiting process in a mapped configuration is the image of a waiting one. -/
theorem map_waiting {f : R₁ → R₂} {g : C₁ → C₂} {procs : List (Proc C₁ R₁)} {i : Nat}
    {c₂ : C₂} {p : Data} {held : List Nat}
    (h : (procs.map (Proc.map f g))[i]? = some ⟨.waiting c₂ p, held⟩) :
    ∃ c, procs[i]? = some ⟨.waiting c p, held⟩ ∧ c₂ = g c := by
  rw [List.getElem?_map] at h
  cases hq : procs[i]? with
  | none => rw [hq] at h; cases h
  | some q =>
    rw [hq] at h
    obtain ⟨st, hl⟩ := q
    cases st with
    | waiting c p' =>
      simp only [Option.map_some, Proc.map, Status.map, Option.some.injEq, Proc.mk.injEq,
        Status.waiting.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨c, rfl, rfl⟩
    | finished r => simp [Proc.map, Status.map] at h

/-- An event on the image of a configuration is the image of that event on
    the configuration. -/
theorem PSim.step_backward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {cfg : Config C₁ R₁} {ev : Event} {cfg₂ : Config C₂ R₂}
    (h : Step S₂ (cfg.map f g) ev cfg₂) :
    ∃ cfg₁, Step S₁ cfg ev cfg₁ ∧ cfg₂ = cfg₁.map f g := by
  generalize hc : cfg.map f g = c₂ at h
  cases h with
  | fresh hi hq hn ht =>
    subst hc
    obtain ⟨c, hi₁, rfl⟩ := map_waiting hi
    obtain ⟨st₁, ht₁, rfl⟩ := s.sim.turn_backward ht
    exact ⟨_, .fresh hi₁ hq hn ht₁, by simp [Config.map, List.map_set, Proc.map]⟩
  | spawn hi hq hs hch ht =>
    subst hc
    obtain ⟨c, hi₁, rfl⟩ := map_waiting hi
    obtain ⟨r₁, hs₁, rfl⟩ := (s.start _ _).mp hs
    obtain ⟨ch₁, hch₁, rfl⟩ := s.sim.settle_backward hch
    obtain ⟨st₁, ht₁, rfl⟩ := s.sim.turn_backward ht
    exact ⟨_, .spawn hi₁ hq hs₁ hch₁ ht₁, by simp [Config.map, List.map_set, Proc.map]⟩
  | comm hi hj hq hq' hh hh' ht ht' =>
    subst hc
    obtain ⟨c, hi₁, rfl⟩ := map_waiting hi
    obtain ⟨c', hj₁, rfl⟩ := map_waiting hj
    obtain ⟨st₁, ht₁, rfl⟩ := s.sim.turn_backward ht
    obtain ⟨st₁', ht₁', rfl⟩ := s.sim.turn_backward ht'
    exact ⟨_, .comm hi₁ hj₁ hq hq' hh hh' ht₁ ht₁', by simp [Config.map, List.map_set, Proc.map]⟩
  | answer hi hq ht =>
    subst hc
    obtain ⟨c, hi₁, rfl⟩ := map_waiting hi
    obtain ⟨st₁, ht₁, rfl⟩ := s.sim.turn_backward ht
    exact ⟨_, .answer hi₁ hq ht₁, by simp [Config.map, List.map_set, Proc.map]⟩

theorem PSim.sched_backward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {c₂ cfg₂ : Config C₂ R₂} {evs : List Event}
    (h : Sched S₂ c₂ evs cfg₂) : ∀ cfg : Config C₁ R₁, c₂ = cfg.map f g →
    ∃ cfg₁, Sched S₁ cfg evs cfg₁ ∧ cfg₂ = cfg₁.map f g := by
  induction h with
  | nil => intro cfg hc; exact ⟨cfg, .nil, hc⟩
  | cons h _ ih =>
    intro cfg hc
    subst hc
    obtain ⟨mid, hm, rfl⟩ := s.step_backward h
    obtain ⟨cfg₁, hr, he⟩ := ih mid rfl
    exact ⟨cfg₁, .cons hm hr, he⟩

/-- A run in the second way of evaluating is the image of a run in the first. -/
theorem PSim.backward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {p : Term} {evs : List Event} {cfg₂ : Config C₂ R₂}
    (h : Network S₂ p evs cfg₂) : ∃ cfg₁, Network S₁ p evs cfg₁ ∧ cfg₂ = cfg₁.map f g := by
  obtain ⟨c, ⟨r₂, st₂, hr, hs, rfl⟩, hd⟩ := h
  obtain ⟨r₁, hr₁, rfl⟩ := (s.start _ _).mp hr
  obtain ⟨st₁, hs₁, rfl⟩ := s.sim.settle_backward hs
  obtain ⟨cfg₁, hd₁, he⟩ := s.sched_backward hd ⟨[⟨st₁, []⟩], []⟩ rfl
  exact ⟨cfg₁, ⟨_, ⟨r₁, st₁, hr₁, hs₁, rfl⟩, hd₁⟩, he⟩

theorem Sim.settle_forward {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {r : R₁} {st : Status C₁ R₁} (h : Settle S₁ r st) :
    Settle S₂ (f r) (st.map f g) := by
  cases h with
  | stop h => exact .stop (by rw [s.fn, h]; rfl)
  | payloadFails h hp hf hd =>
    exact .payloadFails (by rw [s.fn, h]; rfl) ((s.eval _ _ _).mpr ⟨_, hp, rfl⟩)
      (by rw [s.fn, hf]; rfl) (by rw [s.dat, hd])
  | payloadFunction h hp hf =>
    have d : Settle S₂ (f r) (.finished S₂.wrong) :=
      .payloadFunction (by rw [s.fn, h]; rfl) ((s.eval _ _ _).mpr ⟨_, hp, rfl⟩)
        (by rw [s.fn, hf]; rfl)
    rw [← s.wrong] at d
    exact d
  | wait h hp hd =>
    exact .wait (by rw [s.fn, h]; rfl) ((s.eval _ _ _).mpr ⟨_, hp, rfl⟩) (by rw [s.dat, hd])

theorem Sim.turn_forward {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {c : C₁} {a : Data} {st : Status C₁ R₁} (h : Turn S₁ c a st) :
    Turn S₂ (g c) a (st.map f g) := by
  obtain ⟨r, hr, hs⟩ := h
  exact ⟨f r, (s.eval _ _ _).mpr ⟨_, hr, rfl⟩, s.settle_forward hs⟩

theorem waiting_map {f : R₁ → R₂} {g : C₁ → C₂} {procs : List (Proc C₁ R₁)} {i : Nat}
    {c : C₁} {p : Data} {held : List Nat} (h : procs[i]? = some ⟨.waiting c p, held⟩) :
    (procs.map (Proc.map f g))[i]? = some ⟨.waiting (g c) p, held⟩ := by
  rw [List.getElem?_map, h]; rfl

/-- An event on a configuration is the same event on its image. -/
theorem PSim.step_forward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {cfg cfg₁ : Config C₁ R₁} {ev : Event} (h : Step S₁ cfg ev cfg₁) :
    Step S₂ (cfg.map f g) ev (cfg₁.map f g) := by
  cases h with
  | @fresh i n c p held st hi hq hn ht =>
    have e : Config.map f g ⟨cfg.procs.set i ⟨st, n :: held⟩, n :: cfg.names⟩ =
        ⟨(cfg.map f g).procs.set i ⟨st.map f g, n :: held⟩, n :: (cfg.map f g).names⟩ := by
      simp [Config.map, List.map_set, Proc.map]
    rw [e]
    exact .fresh (waiting_map hi) hq hn (s.sim.turn_forward ht)
  | @spawn i c p held t arg r child st hi hq hs hc ht =>
    have e : Config.map f g ⟨cfg.procs.set i ⟨st, held⟩ ++ [⟨child, grant held arg⟩], cfg.names⟩ =
        ⟨(cfg.map f g).procs.set i ⟨st.map f g, held⟩ ++ [⟨child.map f g, grant held arg⟩],
          (cfg.map f g).names⟩ := by
      simp [Config.map, List.map_set, Proc.map]
    rw [e]
    exact .spawn (waiting_map hi) hq ((s.start _ _).mpr ⟨_, hs, rfl⟩) (s.sim.settle_forward hc)
      (s.sim.turn_forward ht)
  | @comm i j c p held c' p' held' ch v st st' hi hj hq hq' hh hh' ht ht' =>
    have e : Config.map f g
          ⟨(cfg.procs.set i ⟨st, held⟩).set j ⟨st', gain held' (grant held v)⟩, cfg.names⟩ =
        ⟨((cfg.map f g).procs.set i ⟨st.map f g, held⟩).set j
          ⟨st'.map f g, gain held' (grant held v)⟩, (cfg.map f g).names⟩ := by
      simp [Config.map, List.map_set, Proc.map]
    rw [e]
    exact .comm (waiting_map hi) (waiting_map hj) hq hq' hh hh' (s.sim.turn_forward ht)
      (s.sim.turn_forward ht')
  | @answer i a c p held st hi hq ht =>
    have e : Config.map f g ⟨cfg.procs.set i ⟨st, held⟩, cfg.names⟩ =
        ⟨(cfg.map f g).procs.set i ⟨st.map f g, held⟩, (cfg.map f g).names⟩ := by
      simp [Config.map, List.map_set, Proc.map]
    rw [e]
    exact .answer (waiting_map hi) hq (s.sim.turn_forward ht)

theorem PSim.sched_forward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {c cfg : Config C₁ R₁} {evs : List Event} (h : Sched S₁ c evs cfg) :
    Sched S₂ (c.map f g) evs (cfg.map f g) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (s.step_forward h) ih

/-- A run in the first way of evaluating has its image as a run in the second. -/
theorem PSim.forward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {p : Term} {evs : List Event} {cfg : Config C₁ R₁}
    (h : Network S₁ p evs cfg) : Network S₂ p evs (cfg.map f g) := by
  obtain ⟨c, ⟨r, st, hr, hs, rfl⟩, hd⟩ := h
  exact ⟨Config.map f g ⟨[⟨st, []⟩], []⟩,
    ⟨f r, st.map f g, (s.start _ _).mpr ⟨_, hr, rfl⟩, s.sim.settle_forward hs, rfl⟩,
    s.sched_forward hd⟩

theorem Status.map_inj {f : R₁ → R₂} {g : C₁ → C₂} (hf : ∀ a b, f a = f b → a = b)
    (hg : ∀ a b, g a = g b → a = b) {s s' : Status C₁ R₁} (h : s.map f g = s'.map f g) :
    s = s' := by
  cases s <;> cases s' <;> simp [Status.map] at h
  · rw [hg _ _ h.1, h.2]
  · rw [hf _ _ h]

theorem Config.map_inj {f : R₁ → R₂} {g : C₁ → C₂} (hf : ∀ a b, f a = f b → a = b)
    (hg : ∀ a b, g a = g b → a = b) {c c' : Config C₁ R₁} (h : c.map f g = c'.map f g) :
    c = c' := by
  obtain ⟨procs, names⟩ := c
  obtain ⟨procs', names'⟩ := c'
  simp only [Config.map, Config.mk.injEq] at h
  obtain ⟨hp, rfl⟩ := h
  have hq : ∀ q q' : Proc C₁ R₁, Proc.map f g q = Proc.map f g q' → q = q' := by
    rintro ⟨st, held⟩ ⟨st', held'⟩ hqq
    simp only [Proc.map, Proc.mk.injEq] at hqq
    rw [Status.map_inj hf hg hqq.1, hqq.2]
  rw [(List.map_inj_right hq).mp hp]

end Generic

variable [Ops]
open MP

theorem sourceP_det : (sourceP : PSys Value Outcome).Det where
  toDet := source_det
  start := fun h h' => direct_deterministic h h'

theorem psim_machine : PSim sourceP machineP MP.injO injV where
  sim := sim_machine
  start := by
    intro t w
    constructor
    · rintro ⟨n, hn⟩
      obtain ⟨o, ho, rfl⟩ := machine_exact t n w hn
      exact ⟨o, ho, rfl⟩
    · rintro ⟨o, hd, rfl⟩
      exact machine_halts_env (env := []) hd

/-- Replay. The configuration a program reaches is a function of the program
    and the schedule. -/
theorem network_deterministic {p : Term} {evs : List Event} {a b : Config Value Outcome}
    (h : Network sourceP p evs a) (h' : Network sourceP p evs b) : a = b :=
  Network.deterministic sourceP_det h h'

/-- A run by direct evaluation is, in compiled form, a run on the machine. -/
theorem network_machine {p : Term} {evs : List Event} {cfg : Config Value Outcome}
    (h : Network sourceP p evs cfg) : Network machineP p evs (cfg.map MP.injO injV) :=
  psim_machine.forward h

/-- Every run on the machine is the compiled form of a run by direct evaluation. -/
theorem network_machine_exact {p : Term} {evs : List Event} {mc : MConfig}
    (h : Network machineP p evs mc) :
    ∃ cfg, Network sourceP p evs cfg ∧ mc = cfg.map MP.injO injV :=
  psim_machine.backward h

theorem psim_interpreted : PSim sourceP interpretedP reifyOutcome reifyValue where
  sim := sim_interpreted
  start := by
    intro t w
    constructor
    · intro h
      obtain ⟨o, ho⟩ := reflective_coverage t _ h
      simp only [Outcome.value.injEq, Value.data.injEq] at ho
      subst ho
      exact ⟨o, (reflective t o).mpr h, rfl⟩
    · rintro ⟨o, hd, rfl⟩
      exact (reflective t o).mp hd

/-- A run by direct evaluation is, as data, a run of the interpreter on data:
    the same schedule, with every evaluation done by the interpreter. -/
theorem network_interpreted {p : Term} {evs : List Event} {cfg : Config Value Outcome}
    (h : Network sourceP p evs cfg) :
    Network interpretedP p evs (cfg.map reifyOutcome reifyValue) :=
  psim_interpreted.forward h

/-- Every run of the interpreter on data is the data form of a run by direct
    evaluation. -/
theorem network_interpreted_exact {p : Term} {evs : List Event} {ic : Config Data Data}
    (h : Network interpretedP p evs ic) :
    ∃ cfg, Network sourceP p evs cfg ∧ ic = cfg.map reifyOutcome reifyValue :=
  psim_interpreted.backward h

/-- The interpreter on data runs a schedule as the program does: a schedule
    leads the program to a configuration exactly when it leads the interpreter
    to that configuration's data form. -/
theorem network_reflective (p : Term) (evs : List Event) (cfg : Config Value Outcome) :
    Network sourceP p evs cfg ↔
    Network interpretedP p evs (cfg.map reifyOutcome reifyValue) := by
  constructor
  · exact network_interpreted
  · intro h
    obtain ⟨cfg₁, h₁, he⟩ := network_interpreted_exact h
    cases Config.map_inj (fun _ _ => reifyOutcome_inj) reifyValue_inj he
    exact h₁

theorem settleRun_sound {budget : Nat} {w : MOutcome} {st : Status MValue MOutcome}
    (h : settleRun budget w = some st) : Settle machine w st := by
  rcases w with (⟨k, e⟩ | d) | i | _
  · rw [settleRun] at h
    split at h
    · next hp =>
      rw [runUntil_eq] at hp
      cases h
      exact Settle.wait (S := machine) rfl ⟨_, hp⟩ rfl
    · next hp =>
      rw [runUntil_eq] at hp
      cases h
      exact Settle.payloadFunction (S := machine) rfl ⟨_, hp⟩ rfl
    · next w' hnd hnf hp =>
      rw [runUntil_eq] at hp
      cases h
      obtain ⟨h1, h2⟩ := payload_other (w' := w') (fun d h => hnd d (by rw [h]))
        (fun k e h => hnf k e (by rw [h]))
      exact Settle.payloadFails (S := machine) rfl ⟨_, hp⟩ h1 h2
    · cases h
  · cases h; exact Settle.stop (S := machine) rfl
  · cases h; exact Settle.stop (S := machine) rfl
  · cases h; exact Settle.stop (S := machine) rfl

theorem turnRun_sound {budget : Nat} {c : MValue} {a : Data} {st : Status MValue MOutcome}
    (h : turnRun budget c a = some st) : Turn machine c a st := by
  unfold turnRun at h
  split at h
  · next w hw =>
    rw [runUntil_eq] at hw
    exact ⟨w, ⟨_, hw⟩, settleRun_sound h⟩
  · cases h

/-- An event the executable scheduler lets through is a `Step`. -/
theorem stepRun_sound {budget : Nat} {cfg cfg' : MConfig} {ev : Event}
    (h : stepRun budget cfg ev = .ok cfg') : Step machineP cfg ev cfg' := by
  cases ev with
  | fresh i n =>
    simp only [stepRun] at h
    split at h
    · next c p held hi =>
      split at h
      · next hq =>
        split at h
        · cases h
        · next hn =>
          split at h
          · next st ht =>
            cases h
            exact .fresh hi hq (by simpa using hn) (turnRun_sound ht)
          · cases h
      · cases h
    · cases h
  | spawn i =>
    simp only [stepRun] at h
    split at h
    · next c p held hi =>
      split at h
      · next t arg hq =>
        split at h
        · next w hw =>
          rw [runUntil_eq] at hw
          split at h
          · next child st hc ht =>
            cases h
            exact .spawn hi hq ⟨_, hw⟩ (settleRun_sound hc) (turnRun_sound ht)
          · cases h
        · cases h
      · cases h
    · cases h
  | comm i j =>
    simp only [stepRun] at h
    split at h
    · next c p held c' p' held' hi hj =>
      split at h
      · next ch v ch' hq hq' =>
        split at h
        · next hcond =>
          simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hcond
          obtain ⟨⟨rfl, hh⟩, hh'⟩ := hcond
          split at h
          · next st st' ht ht' =>
            cases h
            exact .comm hi hj hq hq' hh hh' (turnRun_sound ht) (turnRun_sound ht')
          · cases h
        · cases h
      · cases h
    · cases h
  | answer i a =>
    simp only [stepRun] at h
    split at h
    · next c p held hi =>
      split at h
      · next hq =>
        split at h
        · next st ht =>
          cases h
          exact .answer hi hq (turnRun_sound ht)
        · cases h
      · cases h
    · cases h

/-- The events the executable scheduler reports as done are a schedule, and
    lead to the configuration it reports, however it stopped. -/
theorem schedRun_sound {budget : Nat} : ∀ (evs : List Event) (cfg : MConfig),
    Sched machineP cfg (schedRun budget cfg evs).1 (schedRun budget cfg evs).2.1 := by
  intro evs
  induction evs with
  | nil => intro cfg; exact .nil
  | cons ev evs ih =>
    intro cfg
    rw [schedRun]
    split
    · next mid hm => exact .cons (stepRun_sound hm) (ih mid)
    · exact .nil
    · exact .nil

theorem autoRun_sound {budget : Nat} : ∀ (limit : Nat) (cfg : MConfig),
    Sched machineP cfg (autoRun budget limit cfg).1 (autoRun budget limit cfg).2.1 := by
  intro limit
  induction limit with
  | zero => intro cfg; exact .nil
  | succ limit ih =>
    intro cfg
    rw [autoRun]
    split
    · exact .nil
    · next ev _ =>
      split
      · next mid hm => exact .cons (stepRun_sound hm) (ih mid)
      · exact .nil
      · exact .nil

theorem beginRun_sound {budget : Nat} {p : Term} {cfg : MConfig}
    (h : beginRun budget p = some cfg) : Begin machineP p cfg := by
  unfold beginRun at h
  split at h
  · next w hw =>
    rw [runUntil_eq] at hw
    split at h
    · next st hs => cases h; exact ⟨w, st, ⟨_, hw⟩, settleRun_sound hs, rfl⟩
    · cases h
  · cases h

/-- What the executable scheduler reports after a given schedule is true of
    the program: the events it reports as done are a run of the program by
    direct evaluation, and the configuration it reports is the compiled form of
    where that run leads. This holds however the run stopped. -/
theorem replay_true {budget : Nat} {p : Term} {c₀ : MConfig} (evs : List Event)
    (h : beginRun budget p = some c₀) :
    ∃ cfg, Network sourceP p (schedRun budget c₀ evs).1 cfg ∧
      (schedRun budget c₀ evs).2.1 = cfg.map MP.injO injV :=
  network_machine_exact ⟨c₀, beginRun_sound h, schedRun_sound evs c₀⟩

/-- The same for a schedule the scheduler chose itself. -/
theorem auto_true {budget : Nat} {p : Term} {c₀ : MConfig} (limit : Nat)
    (h : beginRun budget p = some c₀) :
    ∃ cfg, Network sourceP p (autoRun budget limit c₀).1 cfg ∧
      (autoRun budget limit c₀).2.1 = cfg.map MP.injO injV :=
  network_machine_exact ⟨c₀, beginRun_sound h, autoRun_sound limit c₀⟩

end Reflect
