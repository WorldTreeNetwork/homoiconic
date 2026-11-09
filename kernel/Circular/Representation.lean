import Circular.Interpreter
import Circular.Data

namespace Circular

/-- Substitute captured values into a closure, respecting its own binders.
    Missing entries remain free. Quote payloads are never traversed. -/
def closeTerm (env : List Term) (depth : Nat) : Term → Term
  | .var i =>
      if i < depth then .var i
      else match env[i - depth]? with
        | some t => shift depth 0 t
        | none => .var i
  | .lam b => .lam (closeTerm env (depth + 1) b)
  | .app f a => .app (closeTerm env depth f) (closeTerm env depth a)
  | .quote t => .quote t

/-- Syntactic closure readback. This does not evaluate the closure. -/
def readback : Value → Term
  | .closure b env => .lam (closeTerm (env.map readback) 1 b)

/-- Inverse of the exact Church syntax used for indices. -/
def decodeChurch : Term → Option Nat
  | .lam (.lam (.var 0)) => some 0
  | .lam (.lam (.app (.var 1) (.app (.app p (.var 1)) (.var 0)))) =>
      (decodeChurch p).map Nat.succ
  | _ => none

/-- Inverse of the Mogensen–Scott program encoding. It cannot return quote. -/
def decodeProgram : Term → Option Term
  | .lam (.lam (.lam (.app (.var 2) n))) => (decodeChurch n).map Term.var
  | .lam (.lam (.lam (.app (.var 1) b))) => (decodeProgram b).map Term.lam
  | .lam (.lam (.lam (.app (.app (.var 0) f) a))) => do
      return .app (← decodeProgram f) (← decodeProgram a)
  | _ => none

mutual
  /-- A closure carries the abstraction tag, encoded body, and Scott environment. -/
  def decodeClosure : Term → Option Value
    | .lam (.lam (.lam (.app (.app (.var 1) b) env))) => do
        return .closure (← decodeProgram b) (← decodeEnvironment env)
    | _ => none

  def decodeEnvironment : Term → Option Env
    | .lam (.lam (.var 1)) => some []
    | .lam (.lam (.app (.app (.var 0) h) t)) => do
        let .value v ← decodeOutcome h | none
        return v :: (← decodeEnvironment t)
    | _ => none

  def decodeOutcome : Term → Option Outcome
    | .lam (.lam (.app (.var 1) v)) => (decodeClosure v).map Outcome.value
    | .lam (.lam (.app (.var 0) n)) => (decodeChurch n).map Outcome.unbound
    | _ => none
end

/-- Exact data decoding, not observational equivalence or a source evaluation
    predicate. Raw unbound errors and malformed data do not represent outcomes. -/
def Represents (o w : Outcome) : Prop :=
  match w with
  | .value v => decodeOutcome (readback v) = some o
  | .unbound _ => False

@[simp] theorem raw_unbound_does_not_represent : ¬ Represents o (.unbound i) := id

/-- Code values are outside the pure-outcome decoder. -/
def representsEval (o : Outcome) : EvalResult → Prop
  | .pure w => Represents o w
  | .code _ => False

@[simp] theorem code_does_not_represent : ¬ representsEval o (.code t) := id

theorem decodeChurch_church (n : Nat) : decodeChurch (church n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [church, shift_eq_self_of_scoped (church_closed n), decodeChurch,
      ih, Option.map_some]

theorem decodeProgram_encode (h : Pure p) : decodeProgram (encode p h) = some p := by
  induction p with
  | var i =>
    simp only [encode, shift_eq_self_of_scoped (church_closed i), decodeProgram,
      decodeChurch_church, Option.map_some]
  | lam b ih =>
    simp only [encode, shift_eq_self_of_scoped (encode_closed _), decodeProgram,
      ih, Option.map_some]
  | app f a ihf iha =>
    simp only [encode, shift_eq_self_of_scoped (encode_closed _), decodeProgram,
      ihf, iha, Option.bind_some, pure, bind]
  | quote => exact False.elim (not_pure_quote h)

theorem decodeProgram_pure (h : decodeProgram t = some p) : Pure p := by
  induction t using decodeProgram.induct generalizing p with
  | case1 n =>
    simp only [decodeProgram, Option.map_eq_some_iff] at h
    obtain ⟨i, _, rfl⟩ := h
    exact .var _
  | case2 b ih =>
    simp only [decodeProgram, Option.map_eq_some_iff] at h
    obtain ⟨b', hb, rfl⟩ := h
    exact .lam (ih hb)
  | case3 f a ihf iha =>
    simp only [decodeProgram, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨f', hf, a', ha, h⟩ := h
    cases h
    exact .app (ihf hf) (iha ha)
  | case4 => simp_all [decodeProgram]

mutual
  theorem decodeClosure_encodeClosure (v : Value) (h : PureValue v) :
      decodeClosure (encodeClosure v h) = some v := by
    cases v with
    | closure b env =>
      rw [encodeClosure]
      simp only [Data.closure,
        shift_eq_self_of_scoped (encode_closed _),
        shift_eq_self_of_scoped (encodeEnvironment_properties env _).2,
        decodeClosure, decodeProgram_encode, bind, Option.bind_some,
        decodeEnvironment_encodeEnvironment env _, pure]
  termination_by sizeOf v

  theorem decodeEnvironment_encodeEnvironment (env : Env) (h : PureEnv env) :
      decodeEnvironment (encodeEnvironment env h) = some env := by
    cases env with
    | nil => rw [encodeEnvironment]; rfl
    | cons v tail =>
      rw [encodeEnvironment]
      rw [Data.cons,
        shift_eq_self_of_scoped (Data.ok_closed (encodeClosure_properties v _).2),
        shift_eq_self_of_scoped (encodeEnvironment_properties tail _).2]
      simp only [Data.ok, shift_eq_self_of_scoped (encodeClosure_properties v _).2,
        decodeEnvironment, decodeOutcome, decodeClosure_encodeClosure v _,
        Option.map_some, bind, Option.bind_some,
        decodeEnvironment_encodeEnvironment tail _, pure]
  termination_by sizeOf env
end

theorem decodeOutcome_encodeOutcome (h : PureOutcome o) :
    decodeOutcome (encodeOutcome o h) = some o := by
  cases o with
  | value v =>
    simp only [encodeOutcome, Data.ok,
      shift_eq_self_of_scoped (encodeClosure_properties v h).2,
      decodeOutcome, decodeClosure_encodeClosure v h, Option.map_some]
  | unbound i =>
    simp only [encodeOutcome, Data.bad, shift_eq_self_of_scoped (church_closed i),
      decodeOutcome, decodeChurch_church, Option.map_some]

theorem encodeOutcome_injective (h : PureOutcome o) (h' : PureOutcome o')
    (heq : encodeOutcome o h = encodeOutcome o' h') : o = o' := by
  have := congrArg decodeOutcome heq
  simpa only [decodeOutcome_encodeOutcome, Option.some.injEq] using this

theorem Represents_of_readback (h : PureOutcome o)
    (hw : readback v = encodeOutcome o h) : Represents o (.value v) := by
  change decodeOutcome (readback v) = some o
  rw [hw, decodeOutcome_encodeOutcome]

theorem Represents_unique (h : Represents o w) (h' : Represents o' w) : o = o' := by
  cases w with
  | unbound => exact False.elim h
  | value v =>
    change decodeOutcome (readback v) = some o at h
    change decodeOutcome (readback v) = some o' at h'
    exact Option.some.inj (h.symm.trans h')

end Circular
