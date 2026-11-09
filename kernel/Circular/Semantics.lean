import Circular.Syntax

namespace Circular

/-- Environments contain values, never errors or code. -/
inductive Value where
  | closure : Term → List Value → Value
  deriving Repr

abbrev Env := List Value

inductive Outcome where
  | value : Value → Outcome
  | unbound : Nat → Outcome
  deriving Repr

/-- Function-first call by value. There is deliberately no quote rule. -/
inductive Direct : Env → Term → Outcome → Prop where
  | varBound (h : env[i]? = some v) : Direct env (.var i) (.value v)
  | varUnbound (h : env[i]? = none) : Direct env (.var i) (.unbound i)
  | lam : Direct env (.lam b) (.value (.closure b env))
  | appUnbound (hf : Direct env f (.unbound i)) :
      Direct env (.app f a) (.unbound i)
  | appArgUnbound (hf : Direct env f (.value (.closure b captured)))
      (ha : Direct env a (.unbound i)) : Direct env (.app f a) (.unbound i)
  | appValue (hf : Direct env f (.value (.closure b captured)))
      (ha : Direct env a (.value v)) (hb : Direct (v :: captured) b o) :
      Direct env (.app f a) o

/-- The quote rule returns data. Its premise never evaluates the payload. -/
inductive EvalResult where
  | pure : Outcome → EvalResult
  | code : Term → EvalResult
  deriving Repr

inductive Eval : Env → Term → EvalResult → Prop where
  | direct : Direct env t o → Eval env t (.pure o)
  | quote : Eval env (.quote t) (.code t)

theorem direct_deterministic (h : Direct env t o) (h' : Direct env t o') : o = o' := by
  induction h generalizing o' with
  | varBound hv =>
    cases h' with
    | varBound hv' => simp_all
    | varUnbound hv' => simp_all
  | varUnbound hv =>
    cases h' with
    | varBound hv' => simp_all
    | varUnbound => rfl
  | lam => cases h'; rfl
  | appUnbound _ ih =>
    cases h' with
    | appUnbound hf => exact ih hf
    | appArgUnbound hf => cases ih hf
    | appValue hf => cases ih hf
  | appArgUnbound _ _ ihf iha =>
    cases h' with
    | appUnbound hf => cases ihf hf
    | appArgUnbound _ ha => exact iha ha
    | appValue _ ha => cases iha ha
  | appValue _ _ _ ihf iha ihb =>
    cases h' with
    | appUnbound hf => cases ihf hf
    | appArgUnbound _ ha => cases iha ha
    | appValue hf ha hb =>
      cases ihf hf
      cases iha ha
      exact ihb hb

/-- Fuel bounds derivation height. `none` includes exhausted fuel and quote. -/
def evalFuel : Nat → Env → Term → Option Outcome
  | 0, _, _ => none
  | _ + 1, env, .var i =>
      match env[i]? with
      | some v => some (.value v)
      | none => some (.unbound i)
  | _ + 1, env, .lam b => some (.value (.closure b env))
  | n + 1, env, .app f a =>
      match evalFuel n env f with
      | none => none
      | some (.unbound i) => some (.unbound i)
      | some (.value (.closure b captured)) =>
          match evalFuel n env a with
          | none => none
          | some (.unbound i) => some (.unbound i)
          | some (.value v) => evalFuel n (v :: captured) b
  | _ + 1, _, .quote _ => none

theorem evalFuel_sound (h : evalFuel n env t = some o) : Direct env t o := by
  induction n generalizing env t o with
  | zero => simp [evalFuel] at h
  | succ n ih =>
    cases t with
    | var i =>
      simp only [evalFuel] at h
      split at h
      next hv => cases h; exact .varBound hv
      next hv => cases h; exact .varUnbound hv
    | lam b => cases h; exact .lam
    | quote => simp [evalFuel] at h
    | app f a =>
      simp only [evalFuel] at h
      split at h
      next => contradiction
      next hf => cases h; exact .appUnbound (ih hf)
      next hf =>
        split at h
        next => contradiction
        next ha => cases h; exact .appArgUnbound (ih hf) (ih ha)
        next ha => exact .appValue (ih hf) (ih ha) (ih h)

theorem evalFuel_mono (h : evalFuel n env t = some o) (hle : n ≤ m) :
    evalFuel m env t = some o := by
  induction n generalizing env t o m with
  | zero => simp [evalFuel] at h
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      have hle' : n ≤ m := by omega
      cases t with
      | var i => exact h
      | lam b => exact h
      | quote => exact h
      | app f a =>
        simp only [evalFuel] at h ⊢
        split at h
        next => contradiction
        next hf => rw [ih hf hle']; exact h
        next hf =>
          rw [ih hf hle']
          split at h
          next => contradiction
          next ha => rw [ih ha hle']; exact h
          next ha => rw [ih ha hle']; exact ih h hle'

theorem evalFuel_complete (h : Direct env t o) : ∃ n, evalFuel n env t = some o := by
  induction h with
  | varBound hv => exact ⟨1, by simp [evalFuel, hv]⟩
  | varUnbound hv => exact ⟨1, by simp [evalFuel, hv]⟩
  | lam => exact ⟨1, rfl⟩
  | appUnbound _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, hn]⟩
  | appArgUnbound _ _ ihf iha =>
    obtain ⟨nf, hf⟩ := ihf
    obtain ⟨na, ha⟩ := iha
    exact ⟨max nf na + 1, by
      simp [evalFuel, evalFuel_mono hf (Nat.le_max_left ..),
        evalFuel_mono ha (Nat.le_max_right ..)]⟩
  | appValue _ _ _ ihf iha ihb =>
    obtain ⟨nf, hf⟩ := ihf
    obtain ⟨na, ha⟩ := iha
    obtain ⟨nb, hb⟩ := ihb
    let n := max nf (max na nb)
    have hf' := evalFuel_mono hf (m := n) (Nat.le_max_left ..)
    have ha' := evalFuel_mono ha (m := n)
      (Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..))
    have hb' := evalFuel_mono hb (m := n)
      (Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..))
    exact ⟨n + 1, by simp [evalFuel, hf', ha', hb']⟩

theorem direct_iff_evalFuel : Direct env t o ↔ ∃ n, evalFuel n env t = some o :=
  ⟨evalFuel_complete, fun ⟨_, h⟩ => evalFuel_sound h⟩

theorem no_direct_quote : ¬ Direct env (.quote t) o := fun h => by cases h

end Circular
