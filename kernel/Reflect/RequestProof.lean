import Reflect.Request
import Reflect.Correctness
import Reflect.MachineExact
import Reflect.RunUntilProof
import Reflect.SpaceProof

/-!
What is proved about requests.

- `Drive.deterministic`: the requests a run makes and how it ends are fixed by
  where it starts and the answers.
- `Drive.resume`, `Drive.extra`: continuing a waiting run with an answer is the
  same as running from the start with that answer added.
- `Sim.drive`: two ways of evaluating that agree turn by turn agree on whole
  runs. Used for the interpreter and for the machine.
-/
namespace Reflect

section Generic
variable {C R C₁ R₁ C₂ R₂ : Type}

/-- What determinism of a run needs from a way of evaluating. -/
structure Sys.Det (S : Sys C R) : Prop where
  eval : ∀ {c t r r'}, S.eval c t r → S.eval c t r' → r = r'
  excl : ∀ {r c}, S.fn r = some c → S.dat r = none

theorem Drive.deterministic {S : Sys C R} (hS : S.Det) {r : R} {as asked asked' : List Data}
    {e e' : Ending C R} (h : Drive S r as asked e) (h' : Drive S r as asked' e') :
    asked = asked' ∧ e = e' := by
  induction h generalizing asked' e' with
  | stop h =>
    cases h' with
    | stop _ => exact ⟨rfl, rfl⟩
    | payloadFails h2 _ _ _ => rw [h] at h2; cases h2
    | payloadFunction h2 _ _ => rw [h] at h2; cases h2
    | wait h2 _ _ => rw [h] at h2; cases h2
    | answer h2 _ _ _ _ => rw [h] at h2; cases h2
  | payloadFails h hp hf hd =>
    cases h' with
    | stop h2 => rw [h] at h2; cases h2
    | payloadFails h2 hp2 _ _ =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; exact ⟨rfl, rfl⟩
    | payloadFunction h2 hp2 hf2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hf] at hf2; cases hf2
    | wait h2 hp2 hd2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hd] at hd2; cases hd2
    | answer h2 hp2 hd2 _ _ =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hd] at hd2; cases hd2
  | payloadFunction h hp hf =>
    cases h' with
    | stop h2 => rw [h] at h2; cases h2
    | payloadFails h2 hp2 hf2 _ =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hf] at hf2; cases hf2
    | payloadFunction h2 hp2 hf2 => exact ⟨rfl, rfl⟩
    | wait h2 hp2 hd2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2
      rw [hS.excl hf] at hd2; cases hd2
    | answer h2 hp2 hd2 _ _ =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2
      rw [hS.excl hf] at hd2; cases hd2
  | wait h hp hd =>
    cases h' with
    | stop h2 => rw [h] at h2; cases h2
    | payloadFails h2 hp2 _ hd2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hd] at hd2; cases hd2
    | payloadFunction h2 hp2 hf2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2
      rw [hS.excl hf2] at hd; cases hd
    | wait h2 hp2 hd2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hd] at hd2; cases hd2
      exact ⟨rfl, rfl⟩
  | answer h hp hd hr _ ih =>
    cases h' with
    | stop h2 => rw [h] at h2; cases h2
    | payloadFails h2 hp2 _ hd2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hd] at hd2; cases hd2
    | payloadFunction h2 hp2 hf2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2
      rw [hS.excl hf2] at hd; cases hd
    | answer h2 hp2 hd2 hr2 hrest2 =>
      rw [h] at h2; cases h2; cases hS.eval hp hp2; rw [hd] at hd2; cases hd2
      cases hS.eval hr hr2
      obtain ⟨h1, h2⟩ := ih hrest2
      exact ⟨by rw [h1], h2⟩

/-- Continuing a waiting run with an answer is running from the start with
    that answer, and the ones after it, added. -/
theorem Drive.resume {S : Sys C R} {r r' : R} {c : C} {a : Data}
    {as bs asked asked' : List Data} {e : Ending C R}
    (h : Drive S r as asked (.waiting c)) (hr : S.eval c (resumeTerm a) r')
    (hrest : Drive S r' bs asked' e) : Drive S r (as ++ a :: bs) (asked ++ asked') e := by
  generalize hw : Ending.waiting c = w at h
  induction h with
  | stop _ => cases hw
  | payloadFails _ _ _ _ => cases hw
  | payloadFunction _ _ _ => cases hw
  | wait h hp hd => cases hw; exact .answer h hp hd hr hrest
  | answer h hp hd hr' _ ih => exact .answer h hp hd hr' (ih hw)

/-- A run that finished is not changed by more answers. -/
theorem Drive.extra {S : Sys C R} {r x : R} {as asked : List Data} (bs : List Data)
    (h : Drive S r as asked (.finished x)) : Drive S r (as ++ bs) asked (.finished x) := by
  generalize hw : Ending.finished x = w at h
  induction h with
  | stop h => exact .stop h
  | payloadFails h hp hf hd => exact .payloadFails h hp hf hd
  | payloadFunction h hp hf => exact .payloadFunction h hp hf
  | wait _ _ _ => cases hw
  | answer h hp hd hr _ ih => exact .answer h hp hd hr (ih hw)

/-- Two ways of evaluating agree turn by turn, through `f` on results and `g`
    on functions. -/
structure Sim (S₁ : Sys C₁ R₁) (S₂ : Sys C₂ R₂) (f : R₁ → R₂) (g : C₁ → C₂) : Prop where
  fn : ∀ r, S₂.fn (f r) = (S₁.fn r).map g
  dat : ∀ r, S₂.dat (f r) = S₁.dat r
  wrong : f S₁.wrong = S₂.wrong
  eval : ∀ c t r₂, S₂.eval (g c) t r₂ ↔ ∃ r₁, S₁.eval c t r₁ ∧ r₂ = f r₁

theorem Sim.forward {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {r : R₁} {as asked : List Data} {e : Ending C₁ R₁}
    (d : Drive S₁ r as asked e) : Drive S₂ (f r) as asked (e.map f g) := by
  induction d with
  | stop h => exact .stop (by rw [s.fn, h]; rfl)
  | payloadFails h hp hf hd =>
    exact .payloadFails (by rw [s.fn, h]; rfl) ((s.eval _ _ _).mpr ⟨_, hp, rfl⟩)
      (by rw [s.fn, hf]; rfl) (by rw [s.dat, hd])
  | @payloadFunction r c r' c' as h hp hf =>
    have d2 : Drive S₂ (f r) as [] (.finished S₂.wrong) :=
      .payloadFunction (by rw [s.fn, h]; rfl) ((s.eval _ _ _).mpr ⟨_, hp, rfl⟩)
        (by rw [s.fn, hf]; rfl)
    rw [← s.wrong] at d2
    exact d2
  | wait h hp hd =>
    exact .wait (by rw [s.fn, h]; rfl) ((s.eval _ _ _).mpr ⟨_, hp, rfl⟩) (by rw [s.dat, hd])
  | answer h hp hd hr _ ih =>
    exact .answer (by rw [s.fn, h]; rfl) ((s.eval _ _ _).mpr ⟨_, hp, rfl⟩)
      (by rw [s.dat, hd]) ((s.eval _ _ _).mpr ⟨_, hr, rfl⟩) ih

theorem Sim.fn_some {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {r : R₁} {c₂ : C₂} (h : S₂.fn (f r) = some c₂) :
    ∃ c, S₁.fn r = some c ∧ c₂ = g c := by
  rw [s.fn] at h
  cases hx : S₁.fn r with
  | none => rw [hx] at h; cases h
  | some c => rw [hx] at h; cases h; exact ⟨c, rfl, rfl⟩

theorem Sim.fn_none {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {r : R₁} (h : S₂.fn (f r) = none) : S₁.fn r = none := by
  rw [s.fn] at h
  cases hx : S₁.fn r with
  | none => rfl
  | some c => rw [hx] at h; cases h

theorem Sim.backward {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {r₂ : R₂} {as asked : List Data} {e₂ : Ending C₂ R₂}
    (d : Drive S₂ r₂ as asked e₂) :
    ∀ r, r₂ = f r → ∃ e₁, Drive S₁ r as asked e₁ ∧ e₂ = e₁.map f g := by
  induction d with
  | stop h =>
    intro r hr; subst hr
    exact ⟨.finished r, .stop (s.fn_none h), rfl⟩
  | payloadFails h hp hf hd =>
    intro r hr; subst hr
    obtain ⟨c, hc, rfl⟩ := s.fn_some h
    obtain ⟨r₁, hp₁, rfl⟩ := (s.eval _ _ _).mp hp
    exact ⟨.finished r₁, .payloadFails hc hp₁ (s.fn_none hf) (by rw [← s.dat, hd]), rfl⟩
  | payloadFunction h hp hf =>
    intro r hr; subst hr
    obtain ⟨c, hc, rfl⟩ := s.fn_some h
    obtain ⟨r₁, hp₁, rfl⟩ := (s.eval _ _ _).mp hp
    obtain ⟨c', hc', _⟩ := s.fn_some hf
    exact ⟨.finished S₁.wrong, .payloadFunction hc hp₁ hc', by rw [← s.wrong]; rfl⟩
  | wait h hp hd =>
    intro r hr; subst hr
    obtain ⟨c, hc, rfl⟩ := s.fn_some h
    obtain ⟨r₁, hp₁, rfl⟩ := (s.eval _ _ _).mp hp
    exact ⟨.waiting c, .wait hc hp₁ (by rw [← s.dat, hd]), rfl⟩
  | answer h hp hd hr _ ih =>
    intro r hr'; subst hr'
    obtain ⟨c, hc, rfl⟩ := s.fn_some h
    obtain ⟨r₁, hp₁, rfl⟩ := (s.eval _ _ _).mp hp
    obtain ⟨r₂, hr₂, rfl⟩ := (s.eval _ _ _).mp hr
    obtain ⟨e₁, hd₁, he⟩ := ih r₂ rfl
    exact ⟨e₁, .answer hc hp₁ (by rw [← s.dat, hd]) hr₂ hd₁, he⟩

/-- Agreement turn by turn is agreement on whole runs. -/
theorem Sim.drive {S₁ : Sys C₁ R₁} {S₂ : Sys C₂ R₂} {f : R₁ → R₂} {g : C₁ → C₂}
    (s : Sim S₁ S₂ f g) {r : R₁} {as asked : List Data} {e₂ : Ending C₂ R₂} :
    Drive S₂ (f r) as asked e₂ ↔ ∃ e₁, Drive S₁ r as asked e₁ ∧ e₂ = e₁.map f g :=
  ⟨fun d => s.backward d r rfl, fun ⟨_, d, he⟩ => he ▸ s.forward d⟩

theorem Ending.map_inj {f : R₁ → R₂} {g : C₁ → C₂} (hf : ∀ a b, f a = f b → a = b)
    (hg : ∀ a b, g a = g b → a = b) {e e' : Ending C₁ R₁} (h : e.map f g = e'.map f g) :
    e = e' := by
  cases e <;> cases e' <;> simp [Ending.map] at h
  · rw [hf _ _ h]
  · rw [hg _ _ h]

end Generic

variable [Ops]
open MP

theorem source_det : (source : Sys Value Outcome).Det where
  eval := fun h h' => direct_deterministic h h'
  excl := by
    intro r c h
    cases r with
    | value v => cases v <;> simp [source] at h ⊢
    | unbound i => simp [source] at h
    | wrong => simp [source] at h

/-- The interpreter on an open term, at any environment, only produces the
    data form of an outcome of that term. -/
theorem reflective_env_coverage (env : Env) (p : Term) (w : Outcome)
    (h : Direct [] (.app (.app evalTerm (.lit (reify p))) (.lit (.arr (reifyEnv env)))) w) :
    ∃ o, w = .value (.data (reifyOutcome o)) ∧ Direct env p o := by
  have he : evalTerm = .app fixT (.lam (.lam (.lam core))) := rfl
  rw [he, eval_iff .lit .lit] at h
  exact core_sound _ h

theorem sim_interpreted : Sim source interpreted reifyOutcome reifyValue where
  fn := by
    intro r
    cases r with
    | value v => cases v <;> rfl
    | unbound i => rfl
    | wrong => rfl
  dat := by
    intro r
    cases r with
    | value v => cases v <;> rfl
    | unbound i => rfl
    | wrong => rfl
  wrong := rfl
  eval := by
    intro c t w
    constructor
    · intro h
      obtain ⟨o, ho, hd⟩ := reflective_env_coverage [c] t _ h
      simp only [Outcome.value.injEq, Value.data.injEq] at ho
      exact ⟨o, hd, ho⟩
    · rintro ⟨o, hd, rfl⟩
      exact (reflective_env [c] t o).mp hd

/-- The machine started on a compiled term in an environment halts only with
    the compiled form of that term's outcome. -/
theorem machine_exact_env (env : Env) (t : Term) (n : Nat) (w : MOutcome)
    (h : run n (.running (compile t) (injE env) [] []) = .halted w) :
    ∃ o, Direct env t o ∧ w = MP.injO o := by
  rcases rev n t env .done [] [] w h with ⟨e, he, hd⟩ | ⟨m, v, hd, E, hm⟩
  · cases he with
    | unbound i => exact ⟨_, hd, rfl⟩
    | wrong => exact ⟨_, hd, rfl⟩
  · have h1 : run (m + 1) (.running (compile t) (injE env) [] []) =
        .halted (.value (injV v)) := by
      have : run m (.running (compile t) (injE env) [] []) =
          .running .done E [injV v] [] := hm
      rw [run_add, this]; rfl
    exact ⟨_, hd, (halted_unique h1 h).symm⟩

/-- And it does halt with it. -/
theorem machine_halts_env {env : Env} {t : Term} {o : Outcome} (h : Direct env t o) :
    ∃ n, run n (.running (compile t) (injE env) [] []) = .halted (MP.injO o) := by
  have r := MP.fwd h .done [] []
  cases o with
  | value v =>
    obtain ⟨n, E, hn⟩ := r
    refine ⟨n + 1, ?_⟩
    have : run n (.running (compile t) (injE env) [] []) =
        .running .done E [injV v] [] := hn
    rw [run_add, this]; rfl
  | unbound i => exact r
  | wrong => exact r

theorem sim_machine : Sim source machine MP.injO injV where
  fn := by
    intro r
    cases r with
    | value v => cases v <;> rfl
    | unbound i => rfl
    | wrong => rfl
  dat := by
    intro r
    cases r with
    | value v => cases v <;> rfl
    | unbound i => rfl
    | wrong => rfl
  wrong := rfl
  eval := by
    intro c t w
    constructor
    · rintro ⟨n, hn⟩
      exact machine_exact_env [c] t n w hn
    · rintro ⟨o, hd, rfl⟩
      exact machine_halts_env hd

omit [Ops] in
theorem injV_inj (a b : Value) (h : injV a = injV b) : a = b := by
  have := readValue_injV a
  rw [h, readValue_injV] at this
  exact (Option.some.inj this).symm

omit [Ops] in
theorem injO_inj (a b : Outcome) (h : MP.injO a = MP.injO b) : a = b := by
  cases a <;> cases b <;> simp [MP.injO] at h
  · rw [injV_inj _ _ h]
  · rw [h]
  · rfl

/-- Replay. What a program asks and how it ends is a function of the program
    and the answers. -/
theorem interact_deterministic {p : Term} {answers asked asked' : List Data}
    {e e' : Ending Value Outcome} (h : Interact p answers asked e)
    (h' : Interact p answers asked' e') : asked = asked' ∧ e = e' := by
  obtain ⟨o, ho, hd⟩ := h
  obtain ⟨o', ho', hd'⟩ := h'
  cases direct_deterministic ho ho'
  exact Drive.deterministic source_det hd hd'

/-- A waiting program continued with an answer is the program run from the
    start with that answer, and the ones after it, added. -/
theorem interact_resume {p : Term} {c : Value} {a : Data} {o : Outcome}
    {as bs asked asked' : List Data} {e : Ending Value Outcome}
    (h : Interact p as asked (.waiting c)) (hr : Direct [c] (resumeTerm a) o)
    (hrest : Drive source o bs asked' e) : Interact p (as ++ a :: bs) (asked ++ asked') e := by
  obtain ⟨o₀, ho, hd⟩ := h
  exact ⟨o₀, ho, hd.resume hr hrest⟩

/-- A program that finished is not changed by more answers. -/
theorem interact_extra {p : Term} {x : Outcome} {as asked : List Data} (bs : List Data)
    (h : Interact p as asked (.finished x)) : Interact p (as ++ bs) asked (.finished x) := by
  obtain ⟨o, ho, hd⟩ := h
  exact ⟨o, ho, hd.extra bs⟩

/-- The interpreter makes the same requests in the same order, and ends the
    same way, as the program it interprets. -/
theorem interact_reflective (p : Term) (answers asked : List Data) (e : Ending Value Outcome) :
    Interact p answers asked e ↔
    InteractI p answers asked (e.map reifyOutcome reifyValue) := by
  constructor
  · rintro ⟨o, ho, hd⟩
    exact ⟨_, (reflective p o).mp ho, sim_interpreted.forward hd⟩
  · rintro ⟨w, hw, hd⟩
    obtain ⟨o, ho⟩ := reflective_coverage p _ hw
    simp only [Outcome.value.injEq, Value.data.injEq] at ho
    subst ho
    obtain ⟨e₁, hd₁, he⟩ := sim_interpreted.drive.mp hd
    cases Ending.map_inj (fun _ _ => reifyOutcome_inj) reifyValue_inj he
    exact ⟨o, (reflective p o).mpr hw, hd₁⟩

/-- Every interpreted run is the data form of a run of the program. -/
theorem interact_coverage (p : Term) (answers asked : List Data) (e' : Ending Data Data)
    (h : InteractI p answers asked e') :
    ∃ e, e' = e.map reifyOutcome reifyValue ∧ Interact p answers asked e := by
  obtain ⟨w, hw, hd⟩ := h
  obtain ⟨o, ho⟩ := reflective_coverage p _ hw
  simp only [Outcome.value.injEq, Value.data.injEq] at ho
  subst ho
  obtain ⟨e₁, hd₁, he⟩ := sim_interpreted.drive.mp hd
  exact ⟨e₁, he, o, (reflective p o).mpr hw, hd₁⟩

/-- The machine makes the same requests and ends the same way. -/
theorem interact_machine (p : Term) (answers asked : List Data) (e : Ending Value Outcome) :
    Interact p answers asked e ↔ InteractM p answers asked (e.map MP.injO injV) := by
  constructor
  · rintro ⟨o, ho, hd⟩
    obtain ⟨n, hn⟩ := machine_halts_env (env := []) ho
    exact ⟨n, _, hn, sim_machine.forward hd⟩
  · rintro ⟨n, w, hn, hd⟩
    obtain ⟨o, ho, rfl⟩ := machine_exact p n w hn
    obtain ⟨e₁, hd₁, he⟩ := sim_machine.drive.mp hd
    cases Ending.map_inj injO_inj injV_inj he
    exact ⟨o, ho, hd₁⟩

/-- Every machine run is the compiled form of a run of the program. -/
theorem interact_machine_exact (p : Term) (answers asked : List Data)
    (e' : Ending MValue MOutcome) (h : InteractM p answers asked e') :
    ∃ e, e' = e.map MP.injO injV ∧ Interact p answers asked e := by
  obtain ⟨n, w, hn, hd⟩ := h
  obtain ⟨o, ho, rfl⟩ := machine_exact p n w hn
  obtain ⟨e₁, hd₁, he⟩ := sim_machine.drive.mp hd
  exact ⟨e₁, he, o, ho, hd₁⟩

/-- What the executable driver's stop says about the run. -/
def Stop.Holds (w : MOutcome) (as asked : List Data) : Stop → Prop
  | .finished x => Drive machine w as asked (.finished x)
  | .waiting c => Drive machine w as asked (.waiting c)
  | .unfinished => True

theorem payload_other {w' : MOutcome} (hnd : ∀ d, w' ≠ .value (.data d))
    (hnf : ∀ k e, w' ≠ .value (.closure k e)) :
    (machine : Sys MValue MOutcome).fn w' = none ∧ (machine : Sys MValue MOutcome).dat w' = none := by
  cases w' with
  | value v =>
    cases v with
    | closure k e => exact absurd rfl (hnf k e)
    | data d => exact absurd rfl (hnd d)
  | unbound i => exact ⟨rfl, rfl⟩
  | wrong => exact ⟨rfl, rfl⟩

theorem driveRun_sound (budget : Nat) : ∀ (as : List Data) (w : MOutcome),
    (driveRun budget as w).2.Holds w as (driveRun budget as w).1 := by
  intro as
  induction as with
  | nil =>
    intro w
    rcases w with (⟨k, e⟩ | d) | i | _
    · rw [driveRun]
      split
      · next hp =>
        obtain ⟨_, hp⟩ := runTurn_reach hp
        exact Drive.wait (S := machine) rfl ⟨_, hp⟩ rfl
      · next hp =>
        obtain ⟨_, hp⟩ := runTurn_reach hp
        exact Drive.payloadFunction (S := machine) rfl ⟨_, hp⟩ rfl
      · next w' hnd hnf hp =>
        obtain ⟨_, hp⟩ := runTurn_reach hp
        obtain ⟨h1, h2⟩ := payload_other (w' := w') (fun d h => hnd d (by rw [h]))
          (fun k e h => hnf k e (by rw [h]))
        exact Drive.payloadFails (S := machine) rfl ⟨_, hp⟩ h1 h2
      · trivial
    · exact Drive.stop (S := machine) rfl
    · exact Drive.stop (S := machine) rfl
    · exact Drive.stop (S := machine) rfl
  | cons a rest ih =>
    intro w
    rcases w with (⟨k, e⟩ | d) | i | _
    · rw [driveRun]
      split
      · next hp =>
        obtain ⟨_, hp⟩ := runTurn_reach hp
        dsimp only
        split
        · next w' hr =>
          obtain ⟨_, hr⟩ := runTurn_reach hr
          have h := ih w'
          generalize driveRun budget rest w' = res at h
          obtain ⟨asked, s⟩ := res
          cases s with
          | finished x => exact Drive.answer (S := machine) rfl ⟨_, hp⟩ rfl ⟨_, hr⟩ h
          | waiting c => exact Drive.answer (S := machine) rfl ⟨_, hp⟩ rfl ⟨_, hr⟩ h
          | unfinished => trivial
        · trivial
      · next hp =>
        obtain ⟨_, hp⟩ := runTurn_reach hp
        exact Drive.payloadFunction (S := machine) rfl ⟨_, hp⟩ rfl
      · next w' hnd hnf hp =>
        obtain ⟨_, hp⟩ := runTurn_reach hp
        obtain ⟨h1, h2⟩ := payload_other (w' := w') (fun d h => hnd d (by rw [h]))
          (fun k e h => hnf k e (by rw [h]))
        exact Drive.payloadFails (S := machine) rfl ⟨_, hp⟩ h1 h2
      · trivial
    · exact Drive.stop (S := machine) rfl
    · exact Drive.stop (S := machine) rfl
    · exact Drive.stop (S := machine) rfl

/-- What the host's driver reports as finished is a finished run of the
    program, by direct evaluation, with exactly those requests. -/
theorem converse_finished {budget : Nat} {p : Term} {answers asked : List Data} {x : MOutcome}
    (h : converse budget p answers = (asked, .finished x)) :
    ∃ o, x = MP.injO o ∧ Interact p answers asked (.finished o) := by
  unfold converse at h
  split at h
  · next w hw =>
    obtain ⟨_, hw⟩ := runTurn_reach hw
    have hs := driveRun_sound budget answers w
    rw [h] at hs
    obtain ⟨e, he, hi⟩ := interact_machine_exact p answers asked _ ⟨_, w, hw, hs⟩
    cases e with
    | finished o => simp [Ending.map] at he; exact ⟨o, he, hi⟩
    | waiting c => simp [Ending.map] at he
  · cases h

/-- What it reports as waiting is a run waiting on its last request. -/
theorem converse_waiting {budget : Nat} {p : Term} {answers asked : List Data} {c : MValue}
    (h : converse budget p answers = (asked, .waiting c)) :
    ∃ v, c = injV v ∧ Interact p answers asked (.waiting v) := by
  unfold converse at h
  split at h
  · next w hw =>
    obtain ⟨_, hw⟩ := runTurn_reach hw
    have hs := driveRun_sound budget answers w
    rw [h] at hs
    obtain ⟨e, he, hi⟩ := interact_machine_exact p answers asked _ ⟨_, w, hw, hs⟩
    cases e with
    | finished o => simp [Ending.map] at he
    | waiting v => simp [Ending.map] at he; exact ⟨v, he, hi⟩
  · cases h

end Reflect
