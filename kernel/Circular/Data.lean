import Circular.Encoding

namespace Circular

mutual
  /-- Purity of source values includes every captured body and environment. -/
  inductive PureValue : Value → Prop where
    | closure : Pure b → PureEnv env → PureValue (.closure b env)

  inductive PureEnv : Env → Prop where
    | nil : PureEnv []
    | cons : PureValue v → PureEnv env → PureEnv (v :: env)
end

namespace PureValue
theorem body (h : PureValue (.closure b env)) : Pure b := by cases h; assumption
theorem environment (h : PureValue (.closure b env)) : PureEnv env := by cases h; assumption
end PureValue

namespace PureEnv
theorem head (h : PureEnv (v :: env)) : PureValue v := by cases h; assumption
theorem tail (h : PureEnv (v :: env)) : PureEnv env := by cases h; assumption

theorem lookup {i : Nat} (h : PureEnv env) (hv : env[i]? = some v) : PureValue v := by
  induction env generalizing i with
  | nil => simp at hv
  | cons hh ht ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; cases hv; exact h.head
    | succ i => exact ih h.tail hv
end PureEnv

/-- Errors are pure outcomes; code is not an outcome at all. -/
def PureOutcome : Outcome → Prop
  | .value v => PureValue v
  | .unbound _ => True

theorem direct_pure (h : Direct env t o) (ht : Pure t) (he : PureEnv env) : PureOutcome o := by
  induction h with
  | varBound hv => exact he.lookup hv
  | varUnbound => trivial
  | lam => exact .closure (pure_lam.mp ht) he
  | appUnbound => trivial
  | appArgUnbound => trivial
  | appValue hf ha _ ihf iha ihb =>
    have hp := ihf (pure_app.mp ht).1 he
    exact ihb hp.body (.cons (iha (pure_app.mp ht).2 he) hp.environment)

namespace Data
/-- Scott data, with payload shifts made explicit. -/
def nil : Term := .lam (.lam (.var 1))
def cons (h t : Term) : Term := .lam (.lam
  (.app (.app (.var 0) (shift 2 0 h)) (shift 2 0 t)))
def ok (v : Term) : Term := .lam (.lam (.app (.var 1) (shift 2 0 v)))
def bad (i : Nat) : Term := .lam (.lam (.app (.var 0) (shift 2 0 (church i))))
def closure (b env : Term) : Term := .lam (.lam (.lam
  (.app (.app (.var 1) (shift 3 0 b)) (shift 3 0 env))))

theorem nil_pure : Pure nil := .lam (.lam (.var 1))
theorem nil_closed : Closed nil := by decide
theorem cons_pure (hh : Pure h) (ht : Pure t) : Pure (cons h t) :=
  .lam (.lam (.app (.app (.var 0) (shift_pure hh)) (shift_pure ht)))
theorem cons_closed (hh : Closed h) (ht : Closed t) : Closed (cons h t) :=
  ⟨⟨by decide, by simpa using shift_scoped (k := 2) (c := 0) hh⟩,
    by simpa using shift_scoped (k := 2) (c := 0) ht⟩
theorem ok_pure (h : Pure v) : Pure (ok v) := .lam (.lam (.app (.var 1) (shift_pure h)))
theorem ok_closed (h : Closed v) : Closed (ok v) :=
  ⟨by decide, by simpa using shift_scoped (k := 2) (c := 0) h⟩
theorem bad_pure (i : Nat) : Pure (bad i) := .lam (.lam (.app (.var 0) (shift_pure (church_pure i))))
theorem bad_closed (i : Nat) : Closed (bad i) :=
  ⟨by decide, by simpa using shift_scoped (k := 2) (c := 0) (church_closed i)⟩
theorem closure_pure (hb : Pure b) (he : Pure env) : Pure (closure b env) :=
  .lam (.lam (.lam (.app (.app (.var 1) (shift_pure hb)) (shift_pure he))))
theorem closure_closed (hb : Closed b) (he : Closed env) : Closed (closure b env) :=
  ⟨⟨by decide, by simpa using shift_scoped (k := 3) (c := 0) hb⟩,
    by simpa using shift_scoped (k := 3) (c := 0) he⟩
end Data

mutual
  def encodeClosure (v : Value) (h : PureValue v) : Term :=
    match v with
    | .closure b env => Data.closure (encode b h.body) (encodeEnvironment env h.environment)
  termination_by sizeOf v

  def encodeEnvironment (env : Env) (h : PureEnv env) : Term :=
    match env with
    | [] => Data.nil
    | v :: tail => Data.cons (Data.ok (encodeClosure v h.head)) (encodeEnvironment tail h.tail)
  termination_by sizeOf env
end

/-- Exact syntax for the outcome encoding. The proof argument admits all
    pure source outcomes and excludes closures containing quote. -/
def encodeOutcome (o : Outcome) (h : PureOutcome o) : Term :=
  match o with
  | .value v => Data.ok (encodeClosure v h)
  | .unbound i => Data.bad i

mutual
  theorem encodeClosure_properties (v : Value) (h : PureValue v) :
      Pure (encodeClosure v h) ∧ Closed (encodeClosure v h) := by
    cases v with
    | closure b env =>
      rw [encodeClosure]
      obtain ⟨he, hce⟩ := encodeEnvironment_properties env h.environment
      exact ⟨Data.closure_pure (encode_pure _) he, Data.closure_closed (encode_closed _) hce⟩
  termination_by sizeOf v

  theorem encodeEnvironment_properties (env : Env) (h : PureEnv env) :
      Pure (encodeEnvironment env h) ∧ Closed (encodeEnvironment env h) := by
    cases env with
    | nil => rw [encodeEnvironment]; exact ⟨Data.nil_pure, Data.nil_closed⟩
    | cons v tail =>
      rw [encodeEnvironment]
      obtain ⟨hv, hcv⟩ := encodeClosure_properties v h.head
      obtain ⟨ht, hct⟩ := encodeEnvironment_properties tail h.tail
      exact ⟨Data.cons_pure (Data.ok_pure hv) ht, Data.cons_closed (Data.ok_closed hcv) hct⟩
  termination_by sizeOf env
end

theorem encodeOutcome_pure (h : PureOutcome o) : Pure (encodeOutcome o h) := by
  cases o with
  | value v => exact Data.ok_pure (encodeClosure_properties v h).1
  | unbound i => exact Data.bad_pure i

theorem encodeOutcome_closed (h : PureOutcome o) : Closed (encodeOutcome o h) := by
  cases o with
  | value v => exact Data.ok_closed (encodeClosure_properties v h).2
  | unbound i => exact Data.bad_closed i

end Circular
