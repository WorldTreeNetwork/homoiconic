import Reflect.Interpreter
import Reflect.SemanticsProofs

/-!
The simulation, in environment semantics. The interpreter's answer is data,
so no substitution relation or readback is needed.

`γ` is whatever environment the evaluator term was built in. It is carried
along and never looked at.
-/
-- The same normalizing `simp only` runs in every case; not every lemma fires in each.
set_option linter.unusedSimpArgs false

namespace Reflect
open B

/-- The body of the evaluator: `env` at 0, `code` at 1, `self` at 2. -/
def core : Term := compile ["env", "code", "self"] evalBody
def armBody : Term := .app (.var 1) (.lam (.app (.app (.var 1) (.var 1)) (.var 0)))
def selfBody : Term := .app (.app (.var 1) (.var 1)) (.var 0)
def fixT : Term := .lam (.app (.lam armBody) (.lam armBody))

theorem fix_eq (ctx : List String) : compile ctx fix = fixT := rfl
theorem eval_eq (ctx : List String) :
    compile ctx B.eval = .app fixT (.lam (.lam (.lam core))) := rfl

def FV (γ : Env) : Value := .closure (.lam (.lam core)) γ
def armV (γ : Env) : Value := .closure armBody (FV γ :: γ)
def selfV (γ : Env) : Value := .closure selfBody (armV γ :: FV γ :: γ)
def evalV (γ : Env) : Value := .closure (.lam core) (selfV γ :: γ)

/-- The environment in which `core` runs on program `c` and environment `e`. -/
abbrev frame (γ : Env) (c e : Data) : Env := .data e :: .data c :: selfV γ :: γ

theorem eval_value (γ : Env) :
    Direct γ (.app fixT (.lam (.lam (.lam core)))) (.value (evalV γ)) :=
  .appValue .lam .lam (.appValue .lam .lam (.appValue (.varBound rfl) .lam .lam))

theorem self_unroll (γ : Env) (c : Value) :
    Direct (c :: armV γ :: FV γ :: γ) selfBody
      (.value (.closure core (c :: selfV γ :: γ))) :=
  .appValue (.appValue (.varBound rfl) (.varBound rfl)
    (.appValue (.varBound rfl) .lam .lam)) (.varBound rfl) .lam

theorem self_fun {γ ρ : Env} {st ct : Term} {c : Value}
    (hs : Direct ρ st (.value (selfV γ))) (hc : Direct ρ ct (.value c)) :
    Direct ρ (.app st ct) (.value (.closure core (c :: selfV γ :: γ))) :=
  .appValue hs hc (self_unroll γ c)

/-- A recursive call of the evaluator is a run of `core`. -/
theorem self_apply {γ ρ : Env} {st ct et : Term} {c e : Value} {r : Outcome}
    (hs : Direct ρ st (.value (selfV γ))) (hc : Direct ρ ct (.value c))
    (he : Direct ρ et (.value e)) (h : Direct (e :: c :: selfV γ :: γ) core r) :
    Direct ρ (.app (.app st ct) et) r :=
  .appValue (self_fun hs hc) he h

/-! ## Lookup -/

def lookCore : Term := compile ["orig", "env", "n", "go"] lookBody
theorem look_eq (ctx : List String) :
    compile ctx look = .app fixT (.lam (.lam (.lam (.lam lookCore)))) := rfl

def LFV (ρ : Env) : Value := .closure (.lam (.lam (.lam lookCore))) ρ
def armLV (ρ : Env) : Value := .closure armBody (LFV ρ :: ρ)
def selfLV (ρ : Env) : Value := .closure selfBody (armLV ρ :: LFV ρ :: ρ)

def lookResult (env : Env) (i j : Nat) : Data :=
  match env[i]? with
  | some v => .arr [.nat 0, reifyValue v]
  | none => .arr [.nat 1, .nat j]

/-- Walk a known case tree. Scrutinees are variables. -/
macro "walk" : tactic => `(tactic| repeat' (first
  | assumption
  | exact Direct.lit
  | exact Direct.lam
  | exact Direct.varBound rfl
  | apply Direct.caseZero (Direct.varBound rfl)
  | apply Direct.caseSucc (Direct.varBound rfl)
  | apply Direct.caseNil (Direct.varBound rfl)
  | apply Direct.caseCons (Direct.varBound rfl)
  | apply Direct.consArr
  | apply Direct.succNat
  | apply self_apply (Direct.varBound rfl)
  | apply Direct.appValue Direct.lam))

theorem look_core (ρ : Env) (j : Nat) : ∀ (env : Env) (i : Nat),
    Direct (.data (.nat j) :: .data (.arr (reifyEnv env)) :: .data (.nat i) :: selfLV ρ :: ρ)
      lookCore (.value (.data (lookResult env i j))) := by
  intro env
  induction env with
  | nil =>
    intro i
    unfold lookCore
    simp only [reifyEnv, lookResult, List.getElem?_nil]
    walk
  | cons v t ih =>
    intro i
    cases i with
    | zero =>
      unfold lookCore
      simp only [reifyEnv, lookResult, List.getElem?_cons_zero]
      walk
    | succ m =>
      have hm := ih m
      unfold lookCore
      simp only [reifyEnv, lookResult, List.getElem?_cons_succ]
      apply Direct.caseCons (Direct.varBound rfl)
      apply Direct.caseSucc (Direct.varBound rfl)
      refine .appValue (.appValue (.appValue (.varBound rfl) (.varBound rfl) ?_)
        (.varBound rfl) .lam) (.varBound rfl) hm
      exact .appValue (.appValue (.varBound rfl) (.varBound rfl)
        (.appValue (.varBound rfl) .lam .lam)) (.varBound rfl) .lam

/-- Looking up index `i`, reporting `j` on failure. -/
theorem look_apply {ρ : Env} {nt et ot : Term} (ctx : List String) {env : Env} {i j : Nat}
    (hn : Direct ρ nt (.value (.data (.nat i))))
    (he : Direct ρ et (.value (.data (.arr (reifyEnv env)))))
    (ho : Direct ρ ot (.value (.data (.nat j)))) :
    Direct ρ (.app (.app (.app (compile ctx look) nt) et) ot)
      (.value (.data (lookResult env i j))) := by
  rw [look_eq]
  refine .appValue (.appValue (.appValue
    (.appValue .lam .lam (.appValue .lam .lam (.appValue (.varBound rfl) .lam .lam)))
    hn .lam) he .lam) ho (look_core ρ j env i)

/-! ## Forward: a source derivation gives a run of `core` -/

theorem fwd_var (γ : Env) (env : Env) (i : Nat) :
    Direct (frame γ (.nat i) (.arr (reifyEnv env))) core
      (.value (.data (lookResult env i i))) := by
  unfold core
  cases i with
  | zero =>
    apply Direct.caseZero (Direct.varBound rfl)
    exact look_apply _ (.varBound rfl) (.varBound rfl) (.varBound rfl)
  | succ m =>
    apply Direct.caseSucc (Direct.varBound rfl)
    exact look_apply _ (.varBound rfl) (.varBound rfl) (.varBound rfl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem fwd (γ : Env) {env : Env} {p : Term} {o : Outcome} (h : Direct env p o) :
    Direct (frame γ (reify p) (.arr (reifyEnv env))) core
      (.value (.data (reifyOutcome o))) := by
  induction h with
  | @varBound env i v h =>
    have := fwd_var γ env i
    simpa only [lookResult, h, reify, reifyOutcome] using this
  | @varUnbound env i h =>
    have := fwd_var γ env i
    simpa only [lookResult, h, reify, reifyOutcome] using this
  | @appFunError env f e a hf he ih =>
    cases e with
    | value v => exact he.elim
    | unbound j =>
      unfold core
      simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
      walk
    | wrong =>
      unfold core
      simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
      walk
  | @appArgError env f b cap a e hf ha he ihf ih =>
    cases e with
    | value v => exact he.elim
    | unbound j =>
      unfold core
      simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
      walk
    | wrong =>
      unfold core
      simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
      walk
  | @succError env t e h he ih =>
    cases e with
    | value v => exact he.elim
    | unbound j =>
      unfold core
      simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
      walk
    | wrong =>
      unfold core
      simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
      walk
  | @consHeadError env a e b ha he ih =>
    cases e with
    | value v => exact he.elim
    | unbound j =>
      unfold core
      simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
      walk
    | wrong =>
      unfold core
      simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
      walk
  | @consTailError env a x b e ha hb he iha ih =>
    cases e with
    | value v => exact he.elim
    | unbound j =>
      unfold core
      simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
      walk
    | wrong =>
      unfold core
      simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
      walk
  | @caseError env s e z sc n c hs he ih =>
    cases e with
    | value v => exact he.elim
    | unbound j =>
      unfold core
      simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
      walk
    | wrong =>
      unfold core
      simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
      walk
  | @succNat env t k h ih =>
    unfold core
    simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
    cases k <;> walk
  | @consArr env a x b xs ha hb iha ihb =>
    unfold core
    simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
    cases xs <;> walk
  | @succArr env t xs h ih =>
    unfold core
    simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
    cases xs <;> walk
  | @consTailNat env a x b k ha hb iha ihb =>
    unfold core
    simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
    cases k <;> walk
  | _ =>
    unfold core
    simp only [reify, reifyOutcome, reifyValue, reifyEnv] at *
    walk

/-! ## Reverse: a source evaluation that runs out of fuel leaves `core` out of fuel -/

theorem stuck_mono {ρ : Env} {t : Term} {n m : Nat}
    (h : evalFuel n ρ t = none) (hle : m ≤ n) : evalFuel m ρ t = none := by
  cases hm : evalFuel m ρ t with
  | none => rfl
  | some o => rw [evalFuel_mono hm hle] at h; cases h

theorem known {ρ : Env} {t : Term} {o : Outcome} (n : Nat) (hd : Direct ρ t o) :
    evalFuel n ρ t = none ∨ evalFuel n ρ t = some o := by
  cases h : evalFuel n ρ t with
  | none => exact .inl rfl
  | some o' => exact .inr (by rw [direct_deterministic (evalFuel_sound h) hd])

theorem stuck_case_zero {ρ : Env} {s z sc ni c : Term} {n : Nat}
    (hs : Direct ρ s (.value (.data (.nat 0)))) (h : evalFuel (n - 1) ρ z = none) :
    evalFuel n ρ (.dcase s z sc ni c) = none := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [evalFuel]
    rcases known n hs with h' | h' <;> rw [h']
    simpa using h

theorem stuck_case_succ {ρ : Env} {s z sc ni c : Term} {n k : Nat}
    (hs : Direct ρ s (.value (.data (.nat (k + 1)))))
    (h : evalFuel (n - 1) (.data (.nat k) :: ρ) sc = none) :
    evalFuel n ρ (.dcase s z sc ni c) = none := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [evalFuel]
    rcases known n hs with h' | h' <;> rw [h']
    simpa using h

theorem stuck_case_nil {ρ : Env} {s z sc ni c : Term} {n : Nat}
    (hs : Direct ρ s (.value (.data (.arr [])))) (h : evalFuel (n - 1) ρ ni = none) :
    evalFuel n ρ (.dcase s z sc ni c) = none := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [evalFuel]
    rcases known n hs with h' | h' <;> rw [h']
    simpa using h

theorem stuck_case_cons {ρ : Env} {s z sc ni c : Term} {n : Nat} {x : Data} {xs : List Data}
    (hs : Direct ρ s (.value (.data (.arr (x :: xs)))))
    (h : evalFuel (n - 1) (.data (.arr xs) :: .data x :: ρ) c = none) :
    evalFuel n ρ (.dcase s z sc ni c) = none := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [evalFuel]
    rcases known n hs with h' | h' <;> rw [h']
    simpa using h

theorem stuck_app_arg {ρ cap : Env} {f a b : Term} {n : Nat}
    (hf : Direct ρ f (.value (.closure b cap))) (h : evalFuel (n - 1) ρ a = none) :
    evalFuel n ρ (.app f a) = none := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [evalFuel]
    rcases known n hf with h' | h' <;> rw [h']
    simp only [Nat.add_sub_cancel] at h
    rw [h]

theorem stuck_app_body {ρ cap : Env} {f a b : Term} {v : Value} {n : Nat}
    (hf : Direct ρ f (.value (.closure b cap))) (ha : Direct ρ a (.value v))
    (h : evalFuel (n - 1) (v :: cap) b = none) : evalFuel n ρ (.app f a) = none := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [evalFuel]
    rcases known n hf with h' | h' <;> rw [h']
    rcases known n ha with h'' | h'' <;> rw [h'']
    simpa using h

/-- Go down through case forms whose scrutinee is a variable. -/
macro "sdesc" : tactic => `(tactic| repeat (first
  | apply stuck_case_zero (Direct.varBound rfl)
  | apply stuck_case_succ (Direct.varBound rfl)
  | apply stuck_case_nil (Direct.varBound rfl)
  | apply stuck_case_cons (Direct.varBound rfl)))

/-- A bound recursive call whose run is known. -/
macro "scall_val " h:term : tactic => `(tactic|
  refine stuck_app_body Direct.lam
    (self_apply (Direct.varBound rfl) (by walk) (by walk) $h) ?_)

/-- A bound recursive call that runs out of fuel. -/
macro "scall_stuck " h:term : tactic => `(tactic|
  exact stuck_app_arg Direct.lam
    (stuck_app_body (self_fun (Direct.varBound rfl) (by walk)) (by walk)
      (stuck_mono $h (by omega))))

/-- A recursive call in tail position that runs out of fuel. -/
macro "stail " h:term : tactic => `(tactic|
  exact stuck_app_body (self_fun (Direct.varBound rfl) (by walk)) (by walk)
    (stuck_mono $h (by omega)))

/-- Close a goal whose hypothesis says a finished evaluation returned nothing. -/
macro "impossible " h:ident : tactic => `(tactic|
  ((repeat' split at $h:ident) <;> first | contradiction | cases $h:ident | simp_all))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem stuck_core (γ : Env) : ∀ (n : Nat) (env : Env) (p : Term),
    evalFuel n env p = none →
    evalFuel n (frame γ (reify p) (.arr (reifyEnv env))) core = none := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ m ih =>
    intro env p h
    cases p with
    | var i => simp only [evalFuel] at h; impossible h
    | lam b => simp only [evalFuel] at h; cases h
    | lit d => simp only [evalFuel] at h; cases h
    | app f a =>
      simp only [evalFuel] at h
      unfold core
      simp only [reify]
      cases hf : evalFuel m env f with
      | none => sdesc; scall_stuck (ih _ _ hf)
      | some of =>
        rw [hf] at h
        have Ff := fwd γ (evalFuel_sound hf)
        cases of with
        | unbound j => cases h
        | wrong => cases h
        | value vf =>
          cases vf with
          | data d => cases h
          | closure b cap =>
            simp only [] at h
            simp only [reifyOutcome, reifyValue] at Ff
            cases ha : evalFuel m env a with
            | none => sdesc; scall_val Ff; sdesc; scall_stuck (ih _ _ ha)
            | some oa =>
              rw [ha] at h
              have Fa := fwd γ (evalFuel_sound ha)
              cases oa with
              | unbound j => cases h
              | wrong => cases h
              | value v =>
                simp only [] at h
                have hb := ih _ _ h
                simp only [reifyOutcome, reifyEnv] at Fa hb
                sdesc; scall_val Ff; sdesc; scall_val Fa; sdesc; stail hb
    | succ t =>
      simp only [evalFuel] at h
      unfold core
      simp only [reify]
      cases ht : evalFuel m env t with
      | none => sdesc; scall_stuck (ih _ _ ht)
      | some ot => rw [ht] at h; impossible h
    | cons a b =>
      simp only [evalFuel] at h
      unfold core
      simp only [reify]
      cases ha : evalFuel m env a with
      | none => sdesc; scall_stuck (ih _ _ ha)
      | some oa =>
        rw [ha] at h
        have Fa := fwd γ (evalFuel_sound ha)
        cases oa with
        | unbound j => cases h
        | wrong => cases h
        | value va =>
          cases va with
          | closure c cap => cases h
          | data x =>
            simp only [] at h
            simp only [reifyOutcome, reifyValue] at Fa
            cases hb : evalFuel m env b with
            | none => sdesc; scall_val Fa; sdesc; scall_stuck (ih _ _ hb)
            | some ob => rw [hb] at h; impossible h
    | dcase s z sc ni c =>
      simp only [evalFuel] at h
      unfold core
      simp only [reify]
      cases hs : evalFuel m env s with
      | none => sdesc; scall_stuck (ih _ _ hs)
      | some os =>
        rw [hs] at h
        have Fs := fwd γ (evalFuel_sound hs)
        cases os with
        | unbound j => cases h
        | wrong => cases h
        | value vs =>
          cases vs with
          | closure c' cap => cases h
          | data d =>
            simp only [reifyOutcome, reifyValue] at Fs
            cases d with
            | nat k =>
              cases k with
              | zero =>
                simp only [] at h
                have hb := ih _ _ h
                sdesc; scall_val Fs; sdesc; stail hb
              | succ k =>
                simp only [] at h
                have hb := ih _ _ h
                simp only [reifyEnv, reifyValue] at hb
                sdesc; scall_val Fs; sdesc; stail hb
            | arr xs =>
              cases xs with
              | nil =>
                simp only [] at h
                have hb := ih _ _ h
                sdesc; scall_val Fs; sdesc; stail hb
              | cons x xs =>
                simp only [] at h
                have hb := ih _ _ h
                simp only [reifyEnv, reifyValue] at hb
                sdesc; scall_val Fs; sdesc; stail hb

/-! ## The run of `core` and the source derivation are the same thing -/

theorem reify_inj : ∀ {t t' : Term}, reify t = reify t' → t = t' := by
  intro t
  induction t with
  | var i => intro t' h; cases t' <;> simp [reify] at h; rw [h]
  | lam b ih => intro t' h; cases t' <;> simp [reify] at h; rw [ih h]
  | app f a ihf iha => intro t' h; cases t' <;> simp [reify] at h; rw [ihf h.1, iha h.2]
  | lit d => intro t' h; cases t' <;> simp [reify] at h; rw [h]
  | succ t ih => intro t' h; cases t' <;> simp [reify] at h; rw [ih h]
  | cons a b iha ihb => intro t' h; cases t' <;> simp [reify] at h; rw [iha h.1, ihb h.2]
  | dcase s z sc n c ihs ihz ihsc ihn ihc =>
    intro t' h; cases t' <;> simp [reify] at h
    rw [ihs h.1, ihz h.2.1, ihsc h.2.2.1, ihn h.2.2.2.1, ihc h.2.2.2.2]

mutual
  theorem reifyValue_inj : ∀ (v v' : Value), reifyValue v = reifyValue v' → v = v'
    | .closure b e, .closure b' e', h => by
      simp [reifyValue] at h; rw [reify_inj h.1, reifyEnv_inj e e' h.2]
    | .closure _ _, .data _, h => by simp [reifyValue] at h
    | .data _, .closure _ _, h => by simp [reifyValue] at h
    | .data d, .data d', h => by simp [reifyValue] at h; rw [h]
  theorem reifyEnv_inj : ∀ (e e' : List Value), reifyEnv e = reifyEnv e' → e = e'
    | [], [], _ => rfl
    | [], _ :: _, h => by simp [reifyEnv] at h
    | _ :: _, [], h => by simp [reifyEnv] at h
    | v :: vs, v' :: vs', h => by
      simp [reifyEnv] at h; rw [reifyValue_inj v v' h.1, reifyEnv_inj vs vs' h.2]
end

theorem reifyOutcome_inj {o o' : Outcome} (h : reifyOutcome o = reifyOutcome o') : o = o' := by
  cases o <;> cases o' <;> simp [reifyOutcome] at h
  · rw [reifyValue_inj _ _ h]
  · rw [h]
  · rfl

/-- Every run of `core` on a reified program is the data form of a source outcome. -/
theorem core_sound (γ : Env) {env : Env} {p : Term} {w : Outcome}
    (h : Direct (frame γ (reify p) (.arr (reifyEnv env))) core w) :
    ∃ o, w = .value (.data (reifyOutcome o)) ∧ Direct env p o := by
  obtain ⟨n, hn⟩ := evalFuel_complete h
  cases hs : evalFuel n env p with
  | none => rw [stuck_core γ n env p hs] at hn; cases hn
  | some o =>
    have hd := evalFuel_sound hs
    exact ⟨o, direct_deterministic h (fwd γ hd), hd⟩

theorem core_iff (γ : Env) (env : Env) (p : Term) (o : Outcome) :
    Direct env p o ↔
    Direct (frame γ (reify p) (.arr (reifyEnv env))) core (.value (.data (reifyOutcome o))) := by
  constructor
  · exact fwd γ
  · intro h
    obtain ⟨o', heq, hd⟩ := core_sound γ h
    simp only [Outcome.value.injEq, Value.data.injEq] at heq
    rw [reifyOutcome_inj heq]
    exact hd

/-- Applying a known closure to a known value is running its body. -/
theorem app_inv {ρ cap : Env} {f a b : Term} {v : Value} {w : Outcome}
    (hf : Direct ρ f (.value (.closure b cap))) (ha : Direct ρ a (.value v))
    (h : Direct ρ (.app f a) w) : Direct (v :: cap) b w := by
  cases h with
  | appFunError hf' he => cases direct_deterministic hf hf'; exact he.elim
  | appData hf' => cases direct_deterministic hf hf'
  | appArgError hf' ha' he => cases direct_deterministic ha ha'; exact he.elim
  | appValue hf' ha' hb =>
    cases direct_deterministic hf hf'
    cases direct_deterministic ha ha'
    exact hb

/-- Applying the evaluator term to a program and an environment is a run of `core`. -/
theorem eval_iff {ρ : Env} {ct et : Term} {c e : Data} {w : Outcome}
    (hc : Direct ρ ct (.value (.data c))) (he : Direct ρ et (.value (.data e))) :
    Direct ρ (.app (.app (.app fixT (.lam (.lam (.lam core)))) ct) et) w ↔
    Direct (frame ρ c e) core w := by
  have hf : Direct ρ (.app (.app fixT (.lam (.lam (.lam core)))) ct)
      (.value (.closure core (.data c :: selfV ρ :: ρ))) := .appValue (eval_value ρ) hc .lam
  exact ⟨app_inv hf he, .appValue hf he⟩

theorem interp_eq : interp =
    .lam (.app (.app (.app fixT (.lam (.lam (.lam core)))) (.var 0)) (.lit (.arr []))) := rfl

theorem interp_iff (c : Data) (w : Outcome) :
    Direct [] (.app interp (.lit c)) w ↔ Direct (frame [.data c] c (.arr [])) core w := by
  rw [interp_eq]
  constructor
  · intro h
    exact (eval_iff (.varBound rfl) .lit).mp (app_inv .lam .lit h)
  · intro h
    exact .appValue .lam .lit ((eval_iff (.varBound rfl) .lit).mpr h)

end Reflect
