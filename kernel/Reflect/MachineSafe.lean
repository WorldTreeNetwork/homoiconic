import Reflect.RunUntilProof

/-!
The machine's `fault` state is unreachable from compiled code, whether or not
the run halts. The invariant is a stack typing: what each instruction needs of
the values under it was put there by a check that ran earlier.
-/

namespace Reflect
namespace Safe

/-- What is known of a stack entry. Only a check establishes more than `any`. -/
inductive Tag where
  | any | fn | data | num

def Has : Tag → MValue → Prop
  | .any, _ => True
  | .fn, .closure _ _ => True
  | .fn, .data _ => False
  | .data, .data _ => True
  | .data, .closure _ _ => False
  | .num, .data (.nat _) => True
  | .num, .data (.name _) => True
  | .num, _ => False

/-- `CodeOK c ts`: block `c` can run with entries shaped `ts` above the place
    the block started, and ends with exactly one entry there. -/
def CodeOK : Code → List Tag → Prop
  | .done, ts => ts.length = 1
  | .access _ k, ts => CodeOK k (.any :: ts)
  | .closure b k, ts => CodeOK b [] ∧ CodeOK k (.any :: ts)
  | .literal _ k, ts => CodeOK k (.any :: ts)
  | .checkFun k, _ :: ts => CodeOK k (.fn :: ts)
  | .checkFun _, [] => False
  | .apply k, _ :: .fn :: ts => CodeOK k (.any :: ts)
  | .apply _, _ => False
  | .checkData k, _ :: ts => CodeOK k (.data :: ts)
  | .checkData _, [] => False
  | .succ k, _ :: ts => CodeOK k (.any :: ts)
  | .succ _, [] => False
  | .cons k, _ :: .data :: ts => CodeOK k (.any :: ts)
  | .cons _, _ => False
  | .dcase z sc n c k, _ :: ts =>
      CodeOK z [] ∧ CodeOK sc [] ∧ CodeOK n [] ∧ CodeOK c [] ∧ CodeOK k (.any :: ts)
  | .dcase _ _ _ _ _, [] => False
  | .checkNat k, _ :: ts => CodeOK k (.num :: ts)
  | .checkNat _, [] => False
  | .prim k, _ :: .num :: ts => CodeOK k (.any :: ts)
  | .prim _, _ => False

/-- Compiled code is well-formed wherever its continuation is. This holds for
    every term: open and ill-typed terms included. -/
theorem codeOK_comp : ∀ t k ts, CodeOK k (.any :: ts) → CodeOK (comp t k) ts := by
  intro t
  induction t with
  | var i => intro k ts h; exact h
  | lam b ih => intro k ts h; exact ⟨ih _ _ rfl, h⟩
  | app f a ihf iha => intro k ts h; exact ihf _ _ (iha _ _ h)
  | lit d => intro k ts h; exact h
  | succ t ih => intro k ts h; exact ih _ _ h
  | cons a b iha ihb => intro k ts h; exact iha _ _ (ihb _ _ h)
  | dcase s z sc n c ihs ihz ihsc ihn ihc =>
      intro k ts h
      exact ihs _ _ ⟨ihz _ _ rfl, ihsc _ _ rfl, ihn _ _ rfl, ihc _ _ rfl, h⟩
  | prim c x ihc ihx => intro k ts h; exact ihc _ _ (ihx _ _ h)

theorem codeOK_compile (t : Term) : CodeOK (compile t) [] := codeOK_comp t .done [] rfl

mutual
  /-- Every closure in the value holds a well-formed block. -/
  def ValOK : MValue → Prop
    | .closure b cap => CodeOK b [] ∧ EnvOK cap
    | .data _ => True
  def EnvOK : List MValue → Prop
    | [] => True
    | v :: vs => ValOK v ∧ EnvOK vs
end

theorem envOK_get : ∀ (env : List MValue) (i : Nat) (v : MValue),
    EnvOK env → env[i]? = some v → ValOK v := by
  intro env
  induction env with
  | nil => intro i v _ h; simp at h
  | cons x xs ih =>
    intro i v he h
    simp only [EnvOK] at he
    cases i with
    | zero => simp at h; subst h; exact he.1
    | succ i => simp at h; exact ih i v he.2 h

/-- The stack is entries shaped `ts` on top of `rest`. -/
def Fits : List Tag → List MValue → List MValue → Prop
  | [], stk, rest => stk = rest
  | t :: ts, v :: stk, rest => Has t v ∧ Fits ts stk rest
  | _ :: _, [], _ => False

/-- Each pending frame's code can take the one entry its block leaves, on the
    entries that frame's own block had; the bottom block started on nothing. -/
def FramesOK : List Frame → List MValue → Prop
  | [], rest => rest = []
  | fr :: frs, rest =>
      ∃ ts rest', Fits ts rest rest' ∧ CodeOK fr.code (.any :: ts) ∧ EnvOK fr.env ∧
        FramesOK frs rest'

/-- The invariant. No `fault` state satisfies it. -/
def StateOK : State → Prop
  | .running c env stk frs =>
      ∃ ts rest, CodeOK c ts ∧ Fits ts stk rest ∧ FramesOK frs rest ∧ EnvOK env ∧ EnvOK stk
  | .halted _ => True
  | .fault => False

theorem stateOK_load (t : Term) : StateOK (load (compile t)) :=
  ⟨[], [], codeOK_compile t, rfl, rfl, trivial, trivial⟩

theorem StateOK.ne_fault {s : State} (h : StateOK s) : s ≠ .fault := by
  intro e; subst e; exact h

variable [Ops]

/-- One step keeps the invariant. -/
theorem stateOK_step : ∀ s, StateOK s → StateOK (step s) := by
  intro s h
  cases s with
  | halted o => exact h
  | fault => exact h
  | running c env stk frs =>
    obtain ⟨ts, rest, hc, hf, hfr, he, hs⟩ := h
    cases c with
    | done =>
      match ts, hc with
      | [t], _ =>
        cases stk with
        | nil => exact hf.elim
        | cons v stk' =>
          have hrest : stk' = rest := hf.2
          subst hrest
          cases frs with
          | nil =>
            have : stk' = [] := hfr
            subst this
            exact trivial
          | cons fr frs' =>
            obtain ⟨ts', rest', hf', hc', he', hfr'⟩ := hfr
            have hstep : step (.running .done env (v :: stk') (fr :: frs'))
                = .running fr.code fr.env (v :: stk') frs' := by
              cases stk' <;> rfl
            rw [hstep]
            exact ⟨.any :: ts', rest', hc', ⟨trivial, hf'⟩, hfr', he', hs⟩
    | access i k =>
      simp only [step]
      split
      · next v hv =>
        exact ⟨.any :: ts, rest, hc, ⟨trivial, hf⟩, hfr, he, ⟨envOK_get _ _ _ he hv, hs⟩⟩
      · exact trivial
    | closure b k =>
      exact ⟨.any :: ts, rest, hc.2, ⟨trivial, hf⟩, hfr, he, ⟨⟨hc.1, he⟩, hs⟩⟩
    | literal d k =>
      exact ⟨.any :: ts, rest, hc, ⟨trivial, hf⟩, hfr, he, ⟨trivial, hs⟩⟩
    | checkFun k =>
      match ts, stk, hc, hf, hs with
      | _ :: ts', .closure b cap :: stk', hc, hf, hs =>
        exact ⟨.fn :: ts', rest, hc, ⟨trivial, hf.2⟩, hfr, he, hs⟩
      | _ :: ts', .data d :: stk', hc, hf, hs => exact trivial
    | apply k =>
      match ts, stk, hc, hf, hs with
      | _ :: .fn :: ts', a :: .closure b cap :: stk', hc, hf, hs =>
        exact ⟨[], stk', hs.2.1.1, rfl, ⟨ts', rest, hf.2.2, hc, he, hfr⟩,
          ⟨hs.1, hs.2.1.2⟩, hs.2.2⟩
    | checkData k =>
      match ts, stk, hc, hf, hs with
      | _ :: ts', .data d :: stk', hc, hf, hs =>
        exact ⟨.data :: ts', rest, hc, ⟨trivial, hf.2⟩, hfr, he, hs⟩
      | _ :: ts', .closure b cap :: stk', hc, hf, hs => exact trivial
    | succ k =>
      match ts, stk, hc, hf, hs with
      | _ :: ts', .closure b cap :: stk', hc, hf, hs => exact trivial
      | _ :: ts', .data d :: stk', hc, hf, hs =>
        cases d with
        | nat n => exact ⟨.any :: ts', rest, hc, ⟨trivial, hf.2⟩, hfr, he, ⟨trivial, hs.2⟩⟩
        | name n => exact ⟨.any :: ts', rest, hc, ⟨trivial, hf.2⟩, hfr, he, ⟨trivial, hs.2⟩⟩
        | arr xs => exact trivial
        | text cs => exact trivial
    | cons k =>
      match ts, stk, hc, hf, hs with
      | _ :: .data :: ts', v :: .data x :: stk', hc, hf, hs =>
        cases v with
        | closure b cap => exact trivial
        | data d =>
          cases d with
          | nat n => exact trivial
          | name n => exact trivial
          | arr xs =>
            exact ⟨.any :: ts', rest, hc, ⟨trivial, hf.2.2⟩, hfr, he, ⟨trivial, hs.2.2⟩⟩
          | text cs =>
            exact ⟨.any :: ts', rest, hc, ⟨trivial, hf.2.2⟩, hfr, he, ⟨trivial, hs.2.2⟩⟩
    | dcase z sc n c k =>
      match ts, stk, hc, hf, hs with
      | _ :: ts', .closure b cap :: stk', hc, hf, hs => exact trivial
      | _ :: ts', .data d :: stk', hc, hf, hs =>
        obtain ⟨hz, hsc, hn, hcc, hk⟩ := hc
        have hfr' : FramesOK (⟨k, env⟩ :: frs) stk' := ⟨ts', rest, hf.2, hk, he, hfr⟩
        cases d with
        | nat m =>
          cases m with
          | zero => exact ⟨[], stk', hz, rfl, hfr', he, hs.2⟩
          | succ m => exact ⟨[], stk', hsc, rfl, hfr', ⟨trivial, he⟩, hs.2⟩
        | name m =>
          cases m with
          | zero => exact ⟨[], stk', hz, rfl, hfr', he, hs.2⟩
          | succ m => exact ⟨[], stk', hsc, rfl, hfr', ⟨trivial, he⟩, hs.2⟩
        | arr xs =>
          cases xs with
          | nil => exact ⟨[], stk', hn, rfl, hfr', he, hs.2⟩
          | cons x xs => exact ⟨[], stk', hcc, rfl, hfr', ⟨trivial, trivial, he⟩, hs.2⟩
        | text cs =>
          cases cs with
          | nil => exact ⟨[], stk', hn, rfl, hfr', he, hs.2⟩
          | cons ch r => exact ⟨[], stk', hcc, rfl, hfr', ⟨trivial, trivial, he⟩, hs.2⟩
    | checkNat k =>
      match ts, stk, hc, hf, hs with
      | _ :: ts', .closure b cap :: stk', hc, hf, hs => exact trivial
      | _ :: ts', .data d :: stk', hc, hf, hs =>
        cases d with
        | nat n => exact ⟨.num :: ts', rest, hc, ⟨trivial, hf.2⟩, hfr, he, hs⟩
        | name n => exact ⟨.num :: ts', rest, hc, ⟨trivial, hf.2⟩, hfr, he, hs⟩
        | arr xs => exact trivial
        | text cs => exact trivial
    | prim k =>
      match ts, stk, hc, hf, hs with
      | _ :: .num :: ts', v :: .data (.nat n) :: stk', hc, hf, hs =>
        cases v with
        | closure b cap => exact trivial
        | data d =>
          exact ⟨.any :: ts', rest, hc, ⟨trivial, hf.2.2⟩, hfr, he, ⟨trivial, hs.2.2⟩⟩
      | _ :: .num :: ts', v :: .data (.name n) :: stk', hc, hf, hs =>
        cases v with
        | closure b cap => exact trivial
        | data d =>
          exact ⟨.any :: ts', rest, hc, ⟨trivial, hf.2.2⟩, hfr, he, ⟨trivial, hs.2.2⟩⟩

/-- Any number of steps keeps the invariant. -/
theorem stateOK_run : ∀ n s, StateOK s → StateOK (run n s) := by
  intro n
  induction n with
  | zero => intro s h; exact h
  | succ n ih => intro s h; exact ih _ (stateOK_step s h)

/-- So does a priced run, which either takes a step or stops where it is. -/
theorem stateOK_runPriced : ∀ fuel s, StateOK s → StateOK (runPriced fuel s) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro s h
    cases fuel with
    | zero => rw [runPriced]; exact h
    | succ fuel =>
      cases s with
      | halted o => rw [runPriced]; exact h
      | fault => exact h.elim
      | running c e stk frs =>
        rw [runPriced]
        case x_2 => intro o h'; cases h'
        case x_3 => intro h'; cases h'
        split
        · exact ih fuel (by omega) _ (stateOK_step _ h)
        · split
          · exact ih _ (by omega) _ (stateOK_step _ h)
          · exact h

end Safe

variable [Ops]

/-- A compiled program never reaches the fault state, at any step count,
    whether or not it halts. No hypothesis on the term: an open term halts
    with `unbound` and an ill-typed one with `wrong`, neither of which is a
    fault. -/
theorem machine_never_faults (t : Term) (n : Nat) :
    run n (load (compile t)) ≠ .fault :=
  (Safe.stateOK_run n _ (Safe.stateOK_load t)).ne_fault

theorem machine_never_faults_until (t : Term) (n : Nat) :
    runUntil n (load (compile t)) ≠ .fault := by
  rw [runUntil_eq]; exact machine_never_faults t n

/-- The same under a budget with operation costs. Running out of fuel leaves
    the machine in the running state it could not pay to leave; that state is
    not `fault`, and the charge never changes which step is taken. -/
theorem machine_never_faults_priced (t : Term) (fuel : Nat) :
    runPriced fuel (load (compile t)) ≠ .fault :=
  (Safe.stateOK_runPriced fuel _ (Safe.stateOK_load t)).ne_fault

/-- The invariant is needed: `step` does fault on code no term compiles to. -/
theorem fault_reachable_from_uncompiled :
    run 1 (load (.apply .done)) = .fault := rfl

end Reflect
