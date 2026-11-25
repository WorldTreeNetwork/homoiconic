import Reflect.Log
import Reflect.ChannelProof

/-!
What is proved about a log.

* A program and a log lead to at most one state (`log_deterministic`), and the
  state after a log is the state after a prefix carried on through the rest
  (`log_prefix`). This is P13.
* An entry that is already in the log changes nothing (`log_again`,
  `log_redeliver`), and a log does what its first deliveries do (`log_once`).
  This is P14.
* A state reached by a prefix, given the whole log again, reaches what the
  whole log reaches from the start (`log_restart`).
* A VM's run is a run of its program against the answers of the first
  deliveries (`log_interact`).
* In a sealed log, two entries with one identifier are one entry
  (`sealed_same`), so no entry is passed over for a different one
  (`sealed_first`). This needs `key` to give different names to different
  data, which is a hypothesis of both.
* The machine handles a log as direct evaluation does (`log_machine`,
  `log_machine_exact`), and what the executable fold reports is true of the
  program (`vm_true`).
-/
namespace Reflect

section Generic
variable {C R C₁ R₁ C₂ R₂ : Type}

theorem Handle.deterministic {S : Sys C R} (hS : S.Det) {v a b : Vm C R} {e : Entry}
    (ha : Handle S v e a) (hb : Handle S v e b) : a = b := by
  cases ha with
  | repeated h =>
    cases hb with
    | repeated _ => rfl
    | over _ => rfl
    | answer h' _ _ => exact absurd h h'
  | over hs =>
    cases hb with
    | repeated _ => rfl
    | over _ => rfl
    | answer _ hs' _ => rw [hs] at hs'; cases hs'
  | answer h hs ht =>
    cases hb with
    | repeated h' => exact absurd h' h
    | over hs' => rw [hs] at hs'; cases hs'
    | answer _ hs' ht' =>
      rw [hs] at hs'
      cases hs'
      rw [Turn.deterministic hS ht ht']

theorem Replay.deterministic {S : Sys C R} (hS : S.Det) {v a b : Vm C R} {log : List Entry}
    (ha : Replay S v log a) (hb : Replay S v log b) : a = b := by
  induction ha with
  | nil => cases hb; rfl
  | cons h _ ih =>
    cases hb with
    | cons h' rest' =>
      cases Handle.deterministic hS h h'
      exact ih rest'

theorem Boot.deterministic {S : PSys C R} (hS : S.Det) {p : Term} {a b : Vm C R}
    (ha : Boot S p a) (hb : Boot S p b) : a = b := by
  obtain ⟨r, st, hr, hs, rfl⟩ := ha
  obtain ⟨r', st', hr', hs', rfl⟩ := hb
  cases hS.start hr hr'
  cases Settle.deterministic hS.toDet hs hs'
  rfl

theorem Logged.deterministic {S : PSys C R} (hS : S.Det) {p : Term} {log : List Entry}
    {a b : Vm C R} (ha : Logged S p log a) (hb : Logged S p log b) : a = b := by
  obtain ⟨v, hv, hr⟩ := ha
  obtain ⟨v', hv', hr'⟩ := hb
  cases Boot.deterministic hS hv hv'
  exact Replay.deterministic hS.toDet hr hr'

/-- Handling a log is handling a first part and then the rest. -/
theorem Replay.append {S : Sys C R} {v v'' : Vm C R} {l₁ l₂ : List Entry} :
    Replay S v (l₁ ++ l₂) v'' ↔ ∃ v', Replay S v l₁ v' ∧ Replay S v' l₂ v'' := by
  induction l₁ generalizing v with
  | nil => exact ⟨fun h => ⟨v, .nil, h⟩, fun ⟨_, h₁, h₂⟩ => by cases h₁; exact h₂⟩
  | cons e es ih =>
    rw [List.cons_append]
    constructor
    · intro h
      cases h with
      | cons hh rest =>
        obtain ⟨v', h₁, h₂⟩ := ih.mp rest
        exact ⟨v', .cons hh h₁, h₂⟩
    · intro ⟨v', h₁, h₂⟩
      cases h₁ with
      | cons hh rest => exact .cons hh (ih.mpr ⟨v', rest, h₂⟩)

theorem Logged.append {S : PSys C R} {p : Term} {l₁ l₂ : List Entry} {v : Vm C R} :
    Logged S p (l₁ ++ l₂) v ↔ ∃ s, Logged S p l₁ s ∧ Replay S.toSys s l₂ v := by
  constructor
  · intro ⟨v₀, hb, hr⟩
    obtain ⟨s, h₁, h₂⟩ := Replay.append.mp hr
    exact ⟨s, ⟨v₀, hb, h₁⟩, h₂⟩
  · intro ⟨s, ⟨v₀, hb, h₁⟩, h₂⟩
    exact ⟨v₀, hb, Replay.append.mpr ⟨s, h₁, h₂⟩⟩

/-- An entry a VM does not act on leaves it as it is, and nothing else does. -/
theorem Handle.ignores_iff {S : Sys C R} {v v' : Vm C R} {e : Entry} (hi : v.Ignores e) :
    Handle S v e v' ↔ v' = v := by
  constructor
  · intro h
    cases h with
    | repeated _ => rfl
    | over _ => rfl
    | answer h hs _ =>
      rcases hi with hi | ⟨r, hr⟩
      · exact absurd hi h
      · rw [hs] at hr; cases hr
  · intro h
    subst h
    rcases hi with hi | ⟨r, hr⟩
    · exact .repeated hi
    · exact .over hr

theorem Handle.keeps {S : Sys C R} {v v' : Vm C R} {e x : Entry} (h : Handle S v e v')
    (hi : v.Ignores x) : v'.Ignores x := by
  cases h with
  | repeated _ => exact hi
  | over _ => exact hi
  | answer _ hs _ =>
    rcases hi with hi | ⟨r, hr⟩
    · exact .inl (List.mem_cons_of_mem _ hi)
    · rw [hs] at hr; cases hr

theorem Handle.takes {S : Sys C R} {v v' : Vm C R} {e : Entry} (h : Handle S v e v') :
    v'.Ignores e := by
  cases h with
  | repeated h => exact .inl h
  | over hs => exact .inr ⟨_, hs⟩
  | answer _ _ _ => exact .inl List.mem_cons_self

theorem Replay.keeps {S : Sys C R} {v v' : Vm C R} {log : List Entry} {x : Entry}
    (h : Replay S v log v') (hi : v.Ignores x) : v'.Ignores x := by
  induction h with
  | nil => exact hi
  | cons hh _ ih => exact ih (hh.keeps hi)

/-- After a log, the VM acts on none of its entries. -/
theorem Replay.takes {S : Sys C R} {v v' : Vm C R} {log : List Entry} {e : Entry}
    (h : Replay S v log v') (hm : e ∈ log) : v'.Ignores e := by
  induction h with
  | nil => cases hm
  | cons hh rest ih =>
    rcases List.mem_cons.mp hm with he | he
    · subst he; exact rest.keeps hh.takes
    · exact ih he

theorem Replay.ignored {S : Sys C R} {v v' : Vm C R} {log : List Entry}
    (hall : ∀ e, e ∈ log → v.Ignores e) : Replay S v log v' ↔ v' = v := by
  induction log with
  | nil => exact ⟨fun h => by cases h; rfl, fun h => by subst h; exact .nil⟩
  | cons e es ih =>
    have he := hall e List.mem_cons_self
    have hes : ∀ x, x ∈ es → v.Ignores x := fun x hx => hall x (List.mem_cons_of_mem _ hx)
    constructor
    · intro h
      cases h with
      | cons hh rest =>
        cases (Handle.ignores_iff he).mp hh
        exact (ih hes).mp rest
    · intro h
      subst h
      exact .cons ((Handle.ignores_iff he).mpr rfl) ((ih hes).mpr rfl)

/-- A finished VM is where every log leaves it. -/
theorem Replay.finished {S : Sys C R} {v v' : Vm C R} {log : List Entry} {r : R}
    (hs : v.status = .finished r) : Replay S v log v' ↔ v' = v :=
  Replay.ignored (fun _ _ => .inr ⟨r, hs⟩)

/-- Handling an entry that is already in the log leaves the state as it is. -/
theorem Replay.again {S : Sys C R} {v v' v'' : Vm C R} {log : List Entry} {e : Entry}
    (h : Replay S v log v') (hm : e ∈ log) : Handle S v' e v'' ↔ v'' = v' :=
  Handle.ignores_iff (h.takes hm)

/-- An entry delivered again, anywhere later in the log, changes nothing. -/
theorem Replay.redeliver {S : Sys C R} {v v' : Vm C R} {l₁ l₂ : List Entry} {e : Entry}
    (hm : e ∈ l₁) : Replay S v (l₁ ++ e :: l₂) v' ↔ Replay S v (l₁ ++ l₂) v' := by
  rw [Replay.append, Replay.append]
  constructor
  · intro ⟨m, h₁, h₂⟩
    cases h₂ with
    | cons hh rest =>
      cases (h₁.again hm).mp hh
      exact ⟨m, h₁, rest⟩
  · intro ⟨m, h₁, h₂⟩
    exact ⟨m, h₁, .cons ((h₁.again hm).mpr rfl) h₂⟩

/-- A state reached by a log, given that log again and then more, is where the
    more alone leads. -/
theorem Replay.restart {S : Sys C R} {v s t : Vm C R} {l₁ l₂ : List Entry}
    (h : Replay S v l₁ s) : Replay S s (l₁ ++ l₂) t ↔ Replay S s l₂ t := by
  have ign : ∀ m, Replay S s l₁ m ↔ m = s := fun _ => Replay.ignored (fun _ he => h.takes he)
  rw [Replay.append]
  constructor
  · intro ⟨m, h₁, h₂⟩
    cases (ign m).mp h₁
    exact h₂
  · intro h₂
    exact ⟨s, (ign s).mpr rfl, h₂⟩

/-- A log does what its first deliveries do. -/
theorem Replay.once {S : Sys C R} {v v' : Vm C R} {log : List Entry} :
    Replay S v log v' ↔ Replay S v (firsts v.seen log) v' := by
  induction log generalizing v with
  | nil => exact Iff.rfl
  | cons e es ih =>
    by_cases hm : e.id ∈ v.seen
    · have hf : firsts v.seen (e :: es) = firsts v.seen es := by simp [firsts, hm]
      rw [hf, ← ih]
      constructor
      · intro h
        cases h with
        | cons hh rest =>
          cases (Handle.ignores_iff (.inl hm)).mp hh
          exact rest
      · intro h
        exact .cons (.repeated hm) h
    · have hf : firsts v.seen (e :: es) = e :: firsts (e.id :: v.seen) es := by
        simp [firsts, hm]
      rw [hf]
      constructor
      · intro h
        cases h with
        | cons hh rest =>
          cases hh with
          | repeated h' => exact absurd h' hm
          | over hs =>
            cases (Replay.finished hs).mp rest
            exact (Replay.finished hs).mpr rfl
          | answer _ hs ht => exact .cons (.answer hm hs ht) (ih.mp rest)
      · intro h
        cases h with
        | cons hh rest =>
          cases hh with
          | repeated h' => exact absurd h' hm
          | over hs =>
            cases (Replay.finished hs).mp rest
            exact (Replay.finished hs).mpr rfl
          | answer _ hs ht => exact .cons (.answer hm hs ht) (ih.mpr rest)

theorem Settle.drive_finished {S : Sys C R} {r x : R} (h : Settle S r (.finished x))
    (as : List Data) : Drive S r as [] (.finished x) := by
  cases h with
  | stop h => exact .stop h
  | payloadFails h hp hf hd => exact .payloadFails h hp hf hd
  | payloadFunction h hp hf => exact .payloadFunction h hp hf

/-- A log handled from a turn's result is the request driver run on the answers
    of the first deliveries. -/
theorem Replay.drive {S : Sys C R} {log : List Entry} : ∀ {r : R} {st : Status C R}
    {seen : List Data} {v' : Vm C R}, Settle S r st → Replay S ⟨st, seen⟩ log v' →
    ∃ asked, Drive S r ((firsts seen log).map (·.answer)) asked v'.status.ending := by
  induction log with
  | nil =>
    intro r st seen v' hs h
    cases h
    cases hs with
    | stop h => exact ⟨[], .stop h⟩
    | payloadFails h hp hf hd => exact ⟨[], .payloadFails h hp hf hd⟩
    | payloadFunction h hp hf => exact ⟨[], .payloadFunction h hp hf⟩
    | wait h hp hd => exact ⟨[_], .wait h hp hd⟩
  | cons e es ih =>
    intro r st seen v' hs h
    cases h with
    | cons hh rest =>
      by_cases hm : e.id ∈ seen
      · have hf : firsts seen (e :: es) = firsts seen es := by simp [firsts, hm]
        rw [hf]
        cases (Handle.ignores_iff (.inl hm)).mp hh
        exact ih hs rest
      · have hf : firsts seen (e :: es) = e :: firsts (e.id :: seen) es := by
          simp [firsts, hm]
        rw [hf]
        cases hh with
        | repeated h' => exact absurd h' hm
        | over hs' =>
          have hst : st = .finished _ := hs'
          subst hst
          cases (Replay.finished hs').mp rest
          exact ⟨[], hs.drive_finished _⟩
        | answer _ hs' ht =>
          have hst : st = .waiting _ _ := hs'
          subst hst
          obtain ⟨r'', hev, hst'⟩ := ht
          obtain ⟨asked, d⟩ := ih hst' rest
          cases hs with
          | wait h hp hd => exact ⟨_ :: asked, .answer h hp hd hev d⟩

theorem Sim.handle_forward {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {v v' : Vm C₁ R₁} {e : Entry} (h : Handle S₁ v e v') :
    Handle S₂ (v.map f g) e (v'.map f g) := by
  cases h with
  | repeated h => exact .repeated h
  | @over r hs =>
    exact .over (r := f r) (by show v.status.map f g = _; rw [hs]; rfl)
  | @answer c p st h hs ht =>
    exact .answer (c := g c) (p := p) h (by show v.status.map f g = _; rw [hs]; rfl)
      (s.turn_forward ht)

theorem Sim.handle_backward {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {v : Vm C₁ R₁} {w : Vm C₂ R₂} {e : Entry}
    (h : Handle S₂ (v.map f g) e w) : ∃ v', Handle S₁ v e v' ∧ w = v'.map f g := by
  generalize hv : v.map f g = mv at h
  cases h with
  | repeated h => subst hv; exact ⟨v, .repeated h, rfl⟩
  | over hs =>
    subst hv
    have hs' : v.status.map f g = .finished _ := hs
    cases hst : v.status with
    | waiting c p => rw [hst] at hs'; cases hs'
    | finished r => exact ⟨v, .over hst, rfl⟩
  | answer h hs ht =>
    subst hv
    have hs' : v.status.map f g = .waiting _ _ := hs
    cases hst : v.status with
    | finished r => rw [hst] at hs'; cases hs'
    | waiting c p =>
      rw [hst] at hs'
      cases hs'
      obtain ⟨st₁, ht₁, rfl⟩ := s.turn_backward ht
      exact ⟨⟨st₁, e.id :: v.seen⟩, .answer h hst ht₁, rfl⟩

theorem Sim.replay_forward {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {v v' : Vm C₁ R₁} {log : List Entry} (h : Replay S₁ v log v') :
    Replay S₂ (v.map f g) log (v'.map f g) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (s.handle_forward h) ih

theorem Sim.replay_backward {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {w w' : Vm C₂ R₂} {log : List Entry} (h : Replay S₂ w log w') :
    ∀ v : Vm C₁ R₁, w = v.map f g → ∃ v', Replay S₁ v log v' ∧ w' = v'.map f g := by
  induction h with
  | nil => intro v hv; exact ⟨v, .nil, hv⟩
  | cons h _ ih =>
    intro v hv
    subst hv
    obtain ⟨mid, hm, rfl⟩ := s.handle_backward h
    obtain ⟨v', hr, he⟩ := ih mid rfl
    exact ⟨v', .cons hm hr, he⟩

theorem PSim.logged_forward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {p : Term} {log : List Entry} {v : Vm C₁ R₁}
    (h : Logged S₁ p log v) : Logged S₂ p log (v.map f g) := by
  obtain ⟨v₀, ⟨r, st, hr, hs, rfl⟩, hd⟩ := h
  exact ⟨Vm.map f g ⟨st, []⟩,
    ⟨f r, st.map f g, (s.start _ _).mpr ⟨_, hr, rfl⟩, s.sim.settle_forward hs, rfl⟩,
    s.sim.replay_forward hd⟩

theorem PSim.logged_backward {S₁ : PSys C₁ R₁} {S₂ : PSys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : PSim S₁ S₂ f g) {p : Term} {log : List Entry} {w : Vm C₂ R₂}
    (h : Logged S₂ p log w) : ∃ v, Logged S₁ p log v ∧ w = v.map f g := by
  obtain ⟨w₀, ⟨r₂, st₂, hr, hs, rfl⟩, hd⟩ := h
  obtain ⟨r₁, hr₁, rfl⟩ := (s.start _ _).mp hr
  obtain ⟨st₁, hs₁, rfl⟩ := s.sim.settle_backward hs
  obtain ⟨v, hd₁, he⟩ := s.sim.replay_backward hd ⟨st₁, []⟩ rfl
  exact ⟨v, ⟨_, ⟨r₁, st₁, hr₁, hs₁, rfl⟩, hd₁⟩, he⟩

end Generic

/-! Sealed logs. -/

/-- An order that is absent, or is this entry's place. -/
def orderHere (order : Option Nat) (i : Nat) : Prop :=
  ∀ n, order = some n → n = i

/-- A log the host has signed. `signed mark answer` is the host's acceptance
    of that entry's signature; the kernel has no rule for it. A link names
    the data of the entry before it (`prev` at the first), and an order, when
    the entry carries one, is that entry's place. -/
def signedChain (signed : Data → Data → Prop) (key : Data → Data)
    (prev : Data) (i : Nat) : List (Data × Data) → Prop
  | [] => True
  | (mark, answer) :: rest =>
    signed mark answer ∧
      match readLink mark with
      | some (parent, order) =>
        parent = prev ∧ orderHere order i ∧
          signedChain signed key (key (.arr [mark, answer])) (i + 1) rest
      | none => signedChain signed key (key (.arr [mark, answer])) (i + 1) rest

/-- Where the host has accepted the signature, a link names the entry before
    it, and its order, if it has one, is its place. -/
theorem signed_parent {signed : Data → Data → Prop} {key : Data → Data}
    {prev : Data} {i : Nat} {mark answer : Data} {rest : List (Data × Data)}
    {parent : Data} {order : Option Nat}
    (h : signedChain signed key prev i ((mark, answer) :: rest))
    (hk : readLink mark = some (parent, order)) :
    signed mark answer ∧ parent = prev ∧ orderHere order i := by
  simp only [signedChain] at h
  rw [hk] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Two sealed entries with one identifier are one entry, when `key` gives
    different names to different data. -/
theorem sealed_same {key : Data → Data} (inj : Function.Injective key) {e e' : Entry}
    (h : e.Sealed key) (h' : e'.Sealed key) (hid : e.id = e'.id) : e = e' := by
  cases e with | mk i a
  cases e' with | mk i' a'
  obtain ⟨m, hm⟩ := h
  obtain ⟨m', hm'⟩ := h'
  simp only [Entry.seal, Entry.mk.injEq, and_true] at hm hm'
  subst hm hm'
  have hk := inj hid
  simp only [Data.arr.injEq, List.cons.injEq, and_true] at hk
  simp [hk.1, hk.2]

theorem firsts_sub {log : List Entry} : ∀ {seen : List Data} {e : Entry},
    e ∈ firsts seen log → e ∈ log := by
  induction log with
  | nil => intro _ _ h; simp [firsts] at h
  | cons x xs ih =>
    intro seen e h
    by_cases hx : x.id ∈ seen
    · simp only [firsts, hx, ite_true] at h
      exact List.mem_cons_of_mem _ (ih h)
    · simp only [firsts, hx, ite_false, List.mem_cons] at h
      rcases h with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- Every identifier of a log that was not seen before it is the identifier of
    one of its first deliveries. -/
theorem firsts_has {log : List Entry} : ∀ {seen : List Data} {e : Entry},
    e ∈ log → e.id ∉ seen → ∃ e', e' ∈ firsts seen log ∧ e'.id = e.id := by
  induction log with
  | nil => intro _ _ h; simp at h
  | cons x xs ih =>
    intro seen e he hn
    by_cases hx : x.id ∈ seen
    · have hf : firsts seen (x :: xs) = firsts seen xs := by simp [firsts, hx]
      rw [hf]
      rcases List.mem_cons.mp he with h | h
      · exact absurd (h ▸ hx) hn
      · exact ih h hn
    · have hf : firsts seen (x :: xs) = x :: firsts (x.id :: seen) xs := by simp [firsts, hx]
      rw [hf]
      by_cases hid : x.id = e.id
      · exact ⟨x, List.mem_cons_self, hid⟩
      · rcases List.mem_cons.mp he with h | h
        · exact absurd (h ▸ rfl) hid
        · have hn' : e.id ∉ x.id :: seen := by
            intro hm
            rcases List.mem_cons.mp hm with hm | hm
            · exact hid hm.symm
            · exact hn hm
          obtain ⟨e', hm, he'⟩ := ih h hn'
          exact ⟨e', List.mem_cons_of_mem _ hm, he'⟩

/-- In a sealed log no entry is passed over for a different one: every entry
    is among the first deliveries. -/
theorem sealed_first {key : Data → Data} (inj : Function.Injective key) {log : List Entry}
    (hs : ∀ e ∈ log, e.Sealed key) {e : Entry} (he : e ∈ log) : e ∈ firsts [] log := by
  obtain ⟨e', hm, hid⟩ := firsts_has (seen := []) he (by simp)
  have := sealed_same inj (hs e' (firsts_sub hm)) (hs e he) hid
  exact this ▸ hm

variable [Ops]
open MP

/-- P13. The state of a VM is a function of its program and its log. -/
theorem log_deterministic {p : Term} {log : List Entry} {a b : Vm Value Outcome}
    (ha : Logged sourceP p log a) (hb : Logged sourceP p log b) : a = b :=
  Logged.deterministic sourceP_det ha hb

/-- P13. The state after a log is the state after any first part of it,
    carried on through the rest: a state kept part way is a prefix of the log. -/
theorem log_prefix {p : Term} {l₁ l₂ : List Entry} {v : Vm Value Outcome} :
    Logged sourceP p (l₁ ++ l₂) v ↔ ∃ s, Logged sourceP p l₁ s ∧ Replay source s l₂ v :=
  Logged.append

/-- P14. Handling an entry that is already in the log leaves the state as it
    is. -/
theorem log_again {p : Term} {log : List Entry} {v v' : Vm Value Outcome} {e : Entry}
    (h : Logged sourceP p log v) (hm : e ∈ log) : Handle source v e v' ↔ v' = v := by
  obtain ⟨_, _, hr⟩ := h
  exact hr.again hm

/-- P14. An entry delivered again, anywhere later, changes nothing. -/
theorem log_redeliver {p : Term} {l₁ l₂ : List Entry} {e : Entry} {v : Vm Value Outcome}
    (hm : e ∈ l₁) : Logged sourceP p (l₁ ++ e :: l₂) v ↔ Logged sourceP p (l₁ ++ l₂) v := by
  constructor
  · intro ⟨v₀, hb, hr⟩; exact ⟨v₀, hb, (Replay.redeliver hm).mp hr⟩
  · intro ⟨v₀, hb, hr⟩; exact ⟨v₀, hb, (Replay.redeliver hm).mpr hr⟩

/-- P14. A log does what its first deliveries do, in their order. -/
theorem log_once {p : Term} {log : List Entry} {v : Vm Value Outcome} :
    Logged sourceP p log v ↔ Logged sourceP p (firsts [] log) v := by
  constructor
  · intro ⟨v₀, hb, hr⟩
    obtain ⟨r, st, hr', hs, rfl⟩ := hb
    exact ⟨_, ⟨r, st, hr', hs, rfl⟩, Replay.once.mp hr⟩
  · intro ⟨v₀, hb, hr⟩
    obtain ⟨r, st, hr', hs, rfl⟩ := hb
    exact ⟨_, ⟨r, st, hr', hs, rfl⟩, Replay.once.mpr hr⟩

/-- A state reached by a first part of the log, given the whole log, reaches
    what the whole log reaches from the start. -/
theorem log_restart {p : Term} {l₁ l₂ : List Entry} {s v : Vm Value Outcome}
    (h : Logged sourceP p l₁ s) :
    Replay source s (l₁ ++ l₂) v ↔ Logged sourceP p (l₁ ++ l₂) v := by
  obtain ⟨v₀, hb, hr⟩ := h
  refine (hr.restart (l₂ := l₂) (t := v)).trans ?_
  constructor
  · intro h₂; exact Logged.append.mpr ⟨s, ⟨v₀, hb, hr⟩, h₂⟩
  · intro hl
    obtain ⟨s', hs', h₂⟩ := Logged.append.mp hl
    cases Logged.deterministic sourceP_det hs' ⟨v₀, hb, hr⟩
    exact h₂

/-- A VM's run is a run of its program against the answers of the first
    deliveries, in their order. -/
theorem log_interact {p : Term} {log : List Entry} {v : Vm Value Outcome}
    (h : Logged sourceP p log v) :
    ∃ asked, Interact p ((firsts [] log).map (·.answer)) asked v.status.ending := by
  obtain ⟨v₀, ⟨r, st, hr, hs, rfl⟩, rep⟩ := h
  obtain ⟨asked, d⟩ := Replay.drive hs rep
  exact ⟨asked, r, hr, d⟩

/-- A log handled by direct evaluation is, in compiled form, the log handled
    on the machine. -/
theorem log_machine {p : Term} {log : List Entry} {v : Vm Value Outcome}
    (h : Logged sourceP p log v) : Logged machineP p log (v.map MP.injO injV) :=
  psim_machine.logged_forward h

theorem log_machine_exact {p : Term} {log : List Entry} {w : MVm}
    (h : Logged machineP p log w) :
    ∃ v, Logged sourceP p log v ∧ w = v.map MP.injO injV :=
  psim_machine.logged_backward h

theorem handleRun_sound {budget : Nat} {v v' : MVm} {e : Entry}
    (h : handleRun budget (some v) e = some v') : Handle machine v e v' := by
  by_cases hm : e.id ∈ v.seen
  · have hv : handleRun budget (some v) e = some v := by simp [handleRun, hm]
    rw [hv] at h; cases h; exact .repeated hm
  · cases hst : v.status with
    | finished r =>
      have hv : handleRun budget (some v) e = some v := by simp [handleRun, hm, hst]
      rw [hv] at h; cases h; exact .over hst
    | waiting c q =>
      cases ht : turnRun budget c e.answer with
      | none =>
        have hv : handleRun budget (some v) e = none := by simp [handleRun, hm, hst, ht]
        rw [hv] at h; cases h
      | some st =>
        have hv : handleRun budget (some v) e = some ⟨st, e.id :: v.seen⟩ := by
          simp [handleRun, hm, hst, ht]
        rw [hv] at h; cases h; exact .answer hm hst (turnRun_sound ht)

theorem handleRun_none {budget : Nat} (log : List Entry) :
    log.foldl (handleRun budget) none = none := by
  induction log with
  | nil => rfl
  | cons e es ih => exact ih

theorem foldRun_sound {budget : Nat} : ∀ (log : List Entry) (v v' : MVm),
    log.foldl (handleRun budget) (some v) = some v' → Replay machine v log v' := by
  intro log
  induction log with
  | nil => intro v v' h; cases h; exact .nil
  | cons e es ih =>
    intro v v' h
    rw [List.foldl_cons] at h
    cases hm : handleRun budget (some v) e with
    | none => rw [hm, handleRun_none] at h; cases h
    | some mid => rw [hm] at h; exact .cons (handleRun_sound hm) (ih mid v' h)

theorem bootRun_sound {budget : Nat} {p : Term} {v : MVm} (h : bootRun budget p = some v) :
    Boot machineP p v := by
  unfold bootRun at h
  split at h
  · next w hw =>
    obtain ⟨_, hw⟩ := runTurn_reach hw
    split at h
    · next st hs => cases h; exact ⟨w, st, ⟨_, hw⟩, settleRun_sound hs, rfl⟩
    · cases h
  · cases h

/-- The state the executable VM reports after a log is the compiled form of
    the state of the program's VM with that log, by direct evaluation. -/
theorem vm_true {budget : Nat} {p : Term} {log : List Entry} {w : MVm}
    (h : vmRun budget p log = some w) :
    ∃ v, Logged sourceP p log v ∧ w = v.map MP.injO injV := by
  unfold vmRun at h
  cases hb : bootRun budget p with
  | none => rw [hb, handleRun_none] at h; cases h
  | some v₀ =>
    rw [hb] at h
    exact log_machine_exact ⟨v₀, bootRun_sound hb, foldRun_sound log v₀ _ h⟩

end Reflect
