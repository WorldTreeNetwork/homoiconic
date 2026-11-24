import Reflect.Store
import Reflect.MachineProof
import Reflect.Request

namespace Reflect
variable {R : Type}

/-! ## Pieces with no reference -/

mutual
  theorem toData_toP : ∀ d : Data, (d.toP : P R).toData = some d
    | .nat n => by simp [Data.toP, P.toData]
    | .name n => by simp [Data.toP, P.toData]
    | .text t => by simp [Data.toP, P.toData]
    | .arr xs => by simp [Data.toP, toData_listToP xs]
  theorem toData_listToP : ∀ xs : List Data, (Data.listToP xs : P R).toData = some (.arr xs)
    | [] => by simp [Data.listToP, P.toData]
    | x :: xs => by simp [Data.listToP, P.toData, toData_toP x, toData_listToP xs]
end

theorem Data.toP_inj {d d' : Data} (h : (d.toP : P R) = d'.toP) : d = d' := by
  have h1 := toData_toP (R := R) d
  rw [h, toData_toP] at h1
  exact (Option.some.inj h1).symm

mutual
  theorem unf_data (σ : Store R) : ∀ d : Data, Unf σ d.toP d.toP
    | .nat n => by simpa [Data.toP] using Unf.nat
    | .name n => by simpa [Data.toP] using Unf.name
    | .text t => by simpa [Data.toP] using Unf.text
    | .arr xs => by simpa [Data.toP] using unf_list σ xs
  theorem unf_list (σ : Store R) : ∀ xs : List Data, Unf σ (Data.listToP xs) (Data.listToP xs)
    | [] => by simpa [Data.listToP] using Unf.nil
    | x :: xs => by simpa [Data.listToP] using Unf.cons (unf_data σ x) (unf_list σ xs)
end

mutual
  theorem unf_value (σ : Store R) : ∀ v : MValue, Unf σ v.toP v.toP
    | .closure c env => by simpa [MValue.toP] using Unf.closure (c := c) (unf_env σ env)
    | .data d => by simpa [MValue.toP] using unf_data σ d
  theorem unf_env (σ : Store R) : ∀ vs : List MValue, Unf σ (envToP vs) (envToP vs)
    | [] => by simpa [envToP] using Unf.nil
    | v :: vs => by simpa [envToP] using Unf.cons (unf_value σ v) (unf_env σ vs)
end

theorem Data.toP_ne_closure {d : Data} {c e} : (d.toP : P R) ≠ .closure c e := by
  cases d with
  | nat n => simp [Data.toP]
  | name n => simp [Data.toP]
  | text t => simp [Data.toP]
  | arr xs => cases xs <;> simp [Data.toP, Data.listToP]

theorem Data.toP_ne_ref {d : Data} {r} : (d.toP : P R) ≠ .ref r := by
  cases d with
  | nat n => simp [Data.toP]
  | name n => simp [Data.toP]
  | text t => simp [Data.toP]
  | arr xs => cases xs <;> simp [Data.toP, Data.listToP]

theorem toP_ne_ref {v : MValue} {r} : (v.toP : P R) ≠ .ref r := by
  cases v with
  | closure c env => simp [MValue.toP]
  | data d => simpa [MValue.toP] using Data.toP_ne_ref

theorem toP_closure {v : MValue} {c} {e : P R} (h : v.toP = .closure c e) :
    ∃ env, v = .closure c env ∧ e = envToP env := by
  cases v with
  | closure c' env => simp [MValue.toP] at h; exact ⟨env, by simp [h.1], h.2.symm⟩
  | data d => exact absurd h (by simpa [MValue.toP] using Data.toP_ne_closure)

theorem toP_nat {v : MValue} {n} (h : (v.toP : P R) = .nat n) : v = .data (.nat n) := by
  cases v with
  | closure c' env => simp [MValue.toP] at h
  | data d =>
    cases d with
    | nat m => simp [MValue.toP, Data.toP] at h; simp [h]
    | name m => simp [MValue.toP, Data.toP] at h
    | text t => simp [MValue.toP, Data.toP] at h
    | arr xs => cases xs <;> simp [MValue.toP, Data.toP, Data.listToP] at h

theorem toP_name {v : MValue} {n} (h : (v.toP : P R) = .name n) : v = .data (.name n) := by
  cases v with
  | closure c' env => simp [MValue.toP] at h
  | data d =>
    cases d with
    | nat m => simp [MValue.toP, Data.toP] at h
    | name m => simp [MValue.toP, Data.toP] at h; simp [h]
    | text t => simp [MValue.toP, Data.toP] at h
    | arr xs => cases xs <;> simp [MValue.toP, Data.toP, Data.listToP] at h

theorem toP_text {v : MValue} {t} (h : (v.toP : P R) = .text t) : v = .data (.text t) := by
  cases v with
  | closure c' env => simp [MValue.toP] at h
  | data d =>
    cases d with
    | nat m => simp [MValue.toP, Data.toP] at h
    | name m => simp [MValue.toP, Data.toP] at h
    | text t' => simp [MValue.toP, Data.toP] at h; simp [h]
    | arr xs => cases xs <;> simp [MValue.toP, Data.toP, Data.listToP] at h

theorem toP_nil {v : MValue} (h : (v.toP : P R) = .nil) : v = .data (.arr []) := by
  cases v with
  | closure c' env => simp [MValue.toP] at h
  | data d =>
    cases d with
    | nat m => simp [MValue.toP, Data.toP] at h
    | name m => simp [MValue.toP, Data.toP] at h
    | text t => simp [MValue.toP, Data.toP] at h
    | arr xs => cases xs <;> simp [MValue.toP, Data.toP, Data.listToP] at h; rfl

theorem toP_cons {v : MValue} {a b : P R} (h : v.toP = .cons a b) :
    ∃ x xs, v = .data (.arr (x :: xs)) ∧ a = (MValue.data x).toP ∧
      b = (MValue.data (.arr xs)).toP := by
  cases v with
  | closure c' env => simp [MValue.toP] at h
  | data d =>
    cases d with
    | nat m => simp [MValue.toP, Data.toP] at h
    | name m => simp [MValue.toP, Data.toP] at h
    | text t => simp [MValue.toP, Data.toP] at h
    | arr xs =>
      cases xs with
      | nil => simp [MValue.toP, Data.toP, Data.listToP] at h
      | cons x xs =>
        simp [MValue.toP, Data.toP, Data.listToP] at h
        exact ⟨x, xs, rfl, by simp [MValue.toP, h.1], by simp [MValue.toP, Data.toP, h.2]⟩

theorem envToP_nil {env : List MValue} (h : (envToP env : P R) = .nil) : env = [] := by
  cases env <;> simp [envToP] at h; rfl

theorem envToP_cons {env : List MValue} {a b : P R} (h : envToP env = .cons a b) :
    ∃ v vs, env = v :: vs ∧ a = v.toP ∧ b = envToP vs := by
  cases env with
  | nil => simp [envToP] at h
  | cons v vs => simp [envToP] at h; exact ⟨v, vs, rfl, h.1.symm, h.2.symm⟩

/-! ## Resolving -/

theorem Unf.mono {σ τ : Store R} (hle : σ.le τ) {p q} (h : Unf σ p q) : Unf τ p q := by
  induction h with
  | nat => exact .nat
  | name => exact .name
  | text => exact .text
  | nil => exact .nil
  | cons _ _ ih1 ih2 => exact .cons ih1 ih2
  | closure _ ih => exact .closure ih
  | ref hr _ ih => exact .ref (hle _ _ hr) ih

/-- A piece resolves to at most one thing. -/
theorem Unf.unique {σ : Store R} {p q q'} (h : Unf σ p q) (h' : Unf σ p q') : q = q' := by
  induction h generalizing q' with
  | nat => cases h'; rfl
  | name => cases h'; rfl
  | text => cases h'; rfl
  | nil => cases h'; rfl
  | cons _ _ ih1 ih2 => cases h' with | cons a b => rw [ih1 a, ih2 b]
  | closure _ ih => cases h' with | closure a => rw [ih a]
  | ref hr _ ih =>
    cases h' with
    | ref hr' hp' => rw [hr] at hr'; cases hr'; exact ih hp'

theorem UnfD.up {σ : Store R} {d p q} (h : UnfD σ d p q) : ∀ d', d ≤ d' → UnfD σ d' p q := by
  induction h with
  | nat => intro _ _; exact .nat
  | name => intro _ _; exact .name
  | text => intro _ _; exact .text
  | nil => intro _ _; exact .nil
  | cons _ _ ih1 ih2 => intro d' hd; exact .cons (ih1 d' hd) (ih2 d' hd)
  | closure _ ih => intro d' hd; exact .closure (ih d' hd)
  | ref hr _ ih =>
    intro d' hd
    cases d' with
    | zero => omega
    | succ d' => exact .ref hr (ih d' (by omega))

theorem Unf.depth {σ : Store R} {p q} (h : Unf σ p q) : ∃ d, UnfD σ d p q := by
  induction h with
  | nat => exact ⟨0, .nat⟩
  | name => exact ⟨0, .name⟩
  | text => exact ⟨0, .text⟩
  | nil => exact ⟨0, .nil⟩
  | cons _ _ ih1 ih2 =>
    obtain ⟨a, ha⟩ := ih1
    obtain ⟨b, hb⟩ := ih2
    exact ⟨a + b, .cons (ha.up _ (by omega)) (hb.up _ (by omega))⟩
  | closure _ ih => obtain ⟨a, ha⟩ := ih; exact ⟨a, .closure ha⟩
  | ref hr _ ih => obtain ⟨a, ha⟩ := ih; exact ⟨a + 1, .ref hr ha⟩

theorem UnfD.unf {σ : Store R} {d p q} (h : UnfD σ d p q) : Unf σ p q := by
  induction h with
  | nat => exact .nat
  | name => exact .name
  | text => exact .text
  | nil => exact .nil
  | cons _ _ ih1 ih2 => exact .cons ih1 ih2
  | closure _ ih => exact .closure ih
  | ref hr _ ih => exact .ref hr ih

theorem UnfD.zero {σ : Store R} {d p q} (h : UnfD σ d p q) : d = 0 → p = q := by
  induction h with
  | nat => intro _; rfl
  | name => intro _; rfl
  | text => intro _; rfl
  | nil => intro _; rfl
  | cons _ _ ih1 ih2 => intro hd; rw [ih1 hd, ih2 hd]
  | closure _ ih => intro hd; rw [ih hd]
  | ref _ _ _ => intro hd; omega

theorem UnfD.hyd {σ : Store R} : ∀ (p : P R) {d q}, UnfD σ (d + 1) p q →
    ∃ p', p.hyd σ = .ok p' ∧ UnfD σ d p' q
  | .nat n, _, _, h => by cases h; exact ⟨_, rfl, .nat⟩
  | .name n, _, _, h => by cases h; exact ⟨_, rfl, .name⟩
  | .text t, _, _, h => by cases h; exact ⟨_, rfl, .text⟩
  | .nil, _, _, h => by cases h; exact ⟨_, rfl, .nil⟩
  | .cons a b, _, _, h => by
    cases h with
    | cons ha hb =>
      obtain ⟨a', e1, h1⟩ := UnfD.hyd a ha
      obtain ⟨b', e2, h2⟩ := UnfD.hyd b hb
      exact ⟨.cons a' b', by simp [P.hyd, e1, e2], .cons h1 h2⟩
  | .closure c e, _, _, h => by
    cases h with
    | closure he =>
      obtain ⟨e', e1, h1⟩ := UnfD.hyd e he
      exact ⟨.closure c e', by simp [P.hyd, e1], .closure h1⟩
  | .ref r, _, _, h => by
    cases h with
    | ref hr hp => exact ⟨_, by simp [P.hyd, hr], hp⟩

/-! ## More pieces change nothing -/

theorem fetch_mono {σ τ : Store R} (hle : σ.le τ) {r f s} (h : fetch σ r f = .next s) :
    fetch τ r f = .next s := by
  unfold fetch at h ⊢
  cases hr : σ r with
  | none => simp [hr] at h
  | some p => simp [hr] at h; simp [hle _ _ hr, h]

theorem fetch_needs {σ : Store R} {r f r'} (h : fetch σ r f = .needs r') : σ r' = none := by
  unfold fetch at h
  cases hr : σ r with
  | none => simp [hr] at h; rw [← h]; exact hr
  | some p => simp [hr] at h

theorem hyd_mono {σ τ : Store R} (hle : σ.le τ) : ∀ (p : P R) {p'}, p.hyd σ = .ok p' →
    p.hyd τ = .ok p'
  | .nat n, _, h => by simpa [P.hyd] using h
  | .name n, _, h => by simpa [P.hyd] using h
  | .text t, _, h => by simpa [P.hyd] using h
  | .nil, _, h => by simpa [P.hyd] using h
  | .cons a b, _, h => by
    simp only [P.hyd] at h ⊢
    cases ha : a.hyd σ with
    | error r => simp [ha] at h
    | ok a' =>
      cases hb : b.hyd σ with
      | error r => simp [ha, hb] at h
      | ok b' => simp [ha, hb] at h; simp [hyd_mono hle a ha, hyd_mono hle b hb, h]
  | .closure c e, _, h => by
    simp only [P.hyd] at h ⊢
    cases he : e.hyd σ with
    | error r => simp [he] at h
    | ok e' => simp [he] at h; simp [hyd_mono hle e he, h]
  | .ref r, _, h => by
    simp only [P.hyd] at h ⊢
    cases hr : σ r with
    | none => simp [hr] at h
    | some p => simp [hr] at h; simp [hle _ _ hr, h]

theorem hyd_needs {σ : Store R} : ∀ (p : P R) {r}, p.hyd σ = .error r → σ r = none
  | .nat n, _, h => by simp [P.hyd] at h
  | .name n, _, h => by simp [P.hyd] at h
  | .text t, _, h => by simp [P.hyd] at h
  | .nil, _, h => by simp [P.hyd] at h
  | .cons a b, _, h => by
    simp only [P.hyd] at h
    cases ha : a.hyd σ with
    | error r' => simp [ha] at h; rw [← h]; exact hyd_needs a ha
    | ok a' =>
      cases hb : b.hyd σ with
      | error r' => simp [ha, hb] at h; rw [← h]; exact hyd_needs b hb
      | ok b' => simp [ha, hb] at h
  | .closure c e, _, h => by
    simp only [P.hyd] at h
    cases he : e.hyd σ with
    | error r' => simp [he] at h; rw [← h]; exact hyd_needs e he
    | ok e' => simp [he] at h
  | .ref r, _, h => by
    simp only [P.hyd] at h
    cases hr : σ r with
    | none => simp [hr] at h; rw [← h]; exact hr
    | some p => simp [hr] at h


variable [Ops]

theorem lPrim_nat (σ : Store R) (k : Code) (env : P R) (x : P R) (n : Nat) (stk : List (P R))
    (frs : List (PFrame R)) (hx : ∀ b cap, x ≠ .closure b cap) :
    lPrim σ k env (x :: .nat n :: stk) frs =
      match x.toData with
      | some d => .next (.running k env ((Ops.op n d).toP :: stk) frs)
      | none =>
          match x.hyd σ with
          | .ok x' => .next (.running (.prim k) env (x' :: .nat n :: stk) frs)
          | .error r => .needs r := by
  cases x <;> first | rfl | exact absurd rfl (hx _ _)

theorem lPrim_name (σ : Store R) (k : Code) (env : P R) (x : P R) (n : Nat) (stk : List (P R))
    (frs : List (PFrame R)) (hx : ∀ b cap, x ≠ .closure b cap) :
    lPrim σ k env (x :: .name n :: stk) frs =
      match x.toData with
      | some d => .next (.running k env ((Ops.op n d).toP :: stk) frs)
      | none =>
          match x.hyd σ with
          | .ok x' => .next (.running (.prim k) env (x' :: .name n :: stk) frs)
          | .error r => .needs r := by
  cases x <;> first | rfl | exact absurd rfl (hx _ _)

theorem lPrim_mono {σ τ : Store R} (hle : σ.le τ) {k env stk frs} {ps' : PState R}
    (h : lPrim σ k env stk frs = .next ps') : lPrim τ k env stk frs = .next ps' := by
  rcases stk with _ | ⟨x, _ | ⟨y, stk⟩⟩
  · exact h
  · exact h
  · cases y with
    | ref r => exact fetch_mono hle h
    | nat n =>
      by_cases hx : ∀ b cap, x ≠ .closure b cap
      · rw [lPrim_nat _ _ _ _ _ _ _ hx] at h ⊢
        cases hd : x.toData with
        | some d => simpa [hd] using h
        | none =>
          simp only [hd] at h ⊢
          cases hh : x.hyd σ with
          | ok x' => simp only [hh] at h; simp only [hyd_mono hle x hh]; exact h
          | error r => simp [hh] at h
      · cases x <;> first | exact h | exact absurd (by intro b cap hc; cases hc) hx
    | name n =>
      by_cases hx : ∀ b cap, x ≠ .closure b cap
      · rw [lPrim_name _ _ _ _ _ _ _ hx] at h ⊢
        cases hd : x.toData with
        | some d => simpa [hd] using h
        | none =>
          simp only [hd] at h ⊢
          cases hh : x.hyd σ with
          | ok x' => simp only [hh] at h; simp only [hyd_mono hle x hh]; exact h
          | error r => simp [hh] at h
      · cases x <;> first | exact h | exact absurd (by intro b cap hc; cases hc) hx
    | _ => cases x <;> exact h

theorem lstep_mono {σ τ : Store R} (hle : σ.le τ) {ps ps' : PState R}
    (h : lstep σ ps = .next ps') : lstep τ ps = .next ps' := by
  cases ps with
  | halted o => exact h
  | fault => exact h
  | seeking j i cur k env stk frs =>
    cases cur <;> cases i <;> first | exact h | exact fetch_mono hle h
  | running c env stk frs =>
    cases c with
    | done => exact h
    | access i k => exact h
    | closure b k => exact h
    | literal d k => exact h
    | prim k => exact lPrim_mono hle h
    | checkFun k =>
      rcases stk with _ | ⟨x, stk⟩
      · exact h
      · cases x <;> first | exact h | exact fetch_mono hle h
    | checkData k =>
      rcases stk with _ | ⟨x, stk⟩
      · exact h
      · cases x <;> first | exact h | exact fetch_mono hle h
    | succ k =>
      rcases stk with _ | ⟨x, stk⟩
      · exact h
      · cases x <;> first | exact h | exact fetch_mono hle h
    | checkNat k =>
      rcases stk with _ | ⟨x, stk⟩
      · exact h
      · cases x <;> first | exact h | exact fetch_mono hle h
    | dcase z sc n c k =>
      rcases stk with _ | ⟨x, stk⟩
      · exact h
      · cases x with
        | nat m => cases m <;> exact h
        | name m => cases m <;> exact h
        | text t => cases t <;> exact h
        | ref r => exact fetch_mono hle h
        | _ => exact h
    | apply k =>
      rcases stk with _ | ⟨a, _ | ⟨x, stk⟩⟩
      · exact h
      · exact h
      · cases x <;> first | exact h | exact fetch_mono hle h
    | cons k =>
      rcases stk with _ | ⟨a, _ | ⟨x, stk⟩⟩
      · exact h
      · exact h
      · cases x <;> cases a <;> first | exact h | exact fetch_mono hle h

omit [Ops] in
theorem next_needs {s : PState R} {r : R} {α : Prop} (h : LStep.next s = .needs r) : α := by
  cases h

theorem lPrim_needs {σ : Store R} {k env stk frs} {r : R}
    (h : lPrim σ k env stk frs = .needs r) : σ r = none := by
  rcases stk with _ | ⟨x, _ | ⟨y, stk⟩⟩
  · exact next_needs h
  · exact next_needs h
  · cases y with
    | ref r => exact fetch_needs h
    | nat n =>
      by_cases hx : ∀ b cap, x ≠ .closure b cap
      · rw [lPrim_nat _ _ _ _ _ _ _ hx] at h
        cases hd : x.toData with
        | some d => simp [hd] at h
        | none =>
          simp only [hd] at h
          cases hh : x.hyd σ with
          | ok x' => simp [hh] at h
          | error r' => simp [hh] at h; rw [← h]; exact hyd_needs x hh
      · cases x <;> first | exact next_needs h | exact absurd (by intro b cap hc; cases hc) hx
    | name n =>
      by_cases hx : ∀ b cap, x ≠ .closure b cap
      · rw [lPrim_name _ _ _ _ _ _ _ hx] at h
        cases hd : x.toData with
        | some d => simp [hd] at h
        | none =>
          simp only [hd] at h
          cases hh : x.hyd σ with
          | ok x' => simp [hh] at h
          | error r' => simp [hh] at h; rw [← h]; exact hyd_needs x hh
      · cases x <;> first | exact next_needs h | exact absurd (by intro b cap hc; cases hc) hx
    | _ => cases x <;> exact next_needs h

theorem lstep_needs {σ : Store R} {ps : PState R} {r : R}
    (h : lstep σ ps = .needs r) : σ r = none := by
  cases ps with
  | halted o => exact next_needs h
  | fault => exact next_needs h
  | seeking j i cur k env stk frs =>
    cases cur <;> cases i <;> first | exact fetch_needs h | exact next_needs h
  | running c env stk frs =>
    cases c with
    | done =>
      rcases stk with _ | ⟨x, _ | ⟨y, stk⟩⟩ <;> cases frs <;> exact next_needs h
    | access i k => exact next_needs h
    | closure b k => exact next_needs h
    | literal d k => exact next_needs h
    | prim k => exact lPrim_needs h
    | checkFun k =>
      rcases stk with _ | ⟨x, stk⟩
      · exact next_needs h
      · cases x <;> first | exact fetch_needs h | exact next_needs h
    | checkData k =>
      rcases stk with _ | ⟨x, stk⟩
      · exact next_needs h
      · cases x <;> first | exact fetch_needs h | exact next_needs h
    | succ k =>
      rcases stk with _ | ⟨x, stk⟩
      · exact next_needs h
      · cases x <;> first | exact fetch_needs h | exact next_needs h
    | checkNat k =>
      rcases stk with _ | ⟨x, stk⟩
      · exact next_needs h
      · cases x <;> first | exact fetch_needs h | exact next_needs h
    | dcase z sc n c k =>
      rcases stk with _ | ⟨x, stk⟩
      · exact next_needs h
      · cases x with
        | nat m => cases m <;> exact next_needs h
        | name m => cases m <;> exact next_needs h
        | text t => cases t <;> exact next_needs h
        | ref r => exact fetch_needs h
        | _ => exact next_needs h
    | apply k =>
      rcases stk with _ | ⟨a, _ | ⟨x, stk⟩⟩
      · exact next_needs h
      · exact next_needs h
      · cases x <;> first | exact fetch_needs h | exact next_needs h
    | cons k =>
      rcases stk with _ | ⟨a, _ | ⟨x, stk⟩⟩
      · exact next_needs h
      · exact next_needs h
      · cases x <;> cases a <;> first | exact fetch_needs h | exact next_needs h


/-! ## Taking resolved pieces apart -/

section Inversion
omit [Ops]
variable {σ : Store R}

theorem rv_closure {c e v} (h : RValue σ (.closure c e) v) :
    ∃ env, v = .closure c env ∧ REnv σ e env := by
  unfold RValue at h
  generalize hq : v.toP = q at h
  cases h with
  | closure he =>
    obtain ⟨env, rfl, rfl⟩ := toP_closure hq
    exact ⟨env, rfl, he⟩

theorem rv_nat {n v} (h : RValue σ (.nat n) v) : v = .data (.nat n) := by
  unfold RValue at h
  generalize hq : v.toP = q at h
  cases h; exact toP_nat hq

theorem rv_name {n v} (h : RValue σ (.name n) v) : v = .data (.name n) := by
  unfold RValue at h
  generalize hq : v.toP = q at h
  cases h; exact toP_name hq

theorem rv_text {t v} (h : RValue σ (.text t) v) : v = .data (.text t) := by
  unfold RValue at h
  generalize hq : v.toP = q at h
  cases h; exact toP_text hq

theorem rv_nil {v} (h : RValue σ .nil v) : v = .data (.arr []) := by
  unfold RValue at h
  generalize hq : v.toP = q at h
  cases h; exact toP_nil hq

theorem rv_cons {a b v} (h : RValue σ (.cons a b) v) :
    ∃ x xs, v = .data (.arr (x :: xs)) ∧ RValue σ a (.data x) ∧ RValue σ b (.data (.arr xs)) := by
  unfold RValue at h
  generalize hq : v.toP = q at h
  cases h with
  | cons ha hb =>
    obtain ⟨x, xs, rfl, rfl, rfl⟩ := toP_cons hq
    exact ⟨x, xs, rfl, ha, hb⟩

theorem re_nil {env} (h : REnv σ .nil env) : env = [] := by
  unfold REnv at h
  generalize hq : envToP env = q at h
  cases h; exact envToP_nil hq

theorem re_cons {a b env} (h : REnv σ (.cons a b) env) :
    ∃ v vs, env = v :: vs ∧ RValue σ a v ∧ REnv σ b vs := by
  unfold REnv at h
  generalize hq : envToP env = q at h
  cases h with
  | cons ha hb =>
    obtain ⟨v, vs, rfl, rfl, rfl⟩ := envToP_cons hq
    exact ⟨v, vs, rfl, ha, hb⟩

theorem re_nat {n env} (h : REnv σ (.nat n) env) : False := by
  unfold REnv at h
  generalize hq : envToP env = q at h
  cases h; cases env <;> simp [envToP] at hq

theorem re_name {n env} (h : REnv σ (.name n) env) : False := by
  unfold REnv at h
  generalize hq : envToP env = q at h
  cases h; cases env <;> simp [envToP] at hq

theorem re_text {t env} (h : REnv σ (.text t) env) : False := by
  unfold REnv at h
  generalize hq : envToP env = q at h
  cases h; cases env <;> simp [envToP] at hq

theorem re_closure {c e env} (h : REnv σ (.closure c e) env) : False := by
  unfold REnv at h
  generalize hq : envToP env = q at h
  cases h; cases env <;> simp [envToP] at hq

theorem rv_nat_mk {n} : RValue σ (.nat n) (.data (.nat n)) := by
  simpa [RValue, MValue.toP, Data.toP] using (Unf.nat : Unf σ (.nat n) (.nat n))

theorem rv_name_mk {n} : RValue σ (.name n) (.data (.name n)) := by
  simpa [RValue, MValue.toP, Data.toP] using (Unf.name : Unf σ (.name n) (.name n))

theorem rv_text_mk {t} : RValue σ (.text t) (.data (.text t)) := by
  simpa [RValue, MValue.toP, Data.toP] using (Unf.text : Unf σ (.text t) (.text t))

theorem rv_nil_mk : RValue σ .nil (.data (.arr [])) := by
  simpa [RValue, MValue.toP, Data.toP, Data.listToP] using (Unf.nil : Unf σ .nil .nil)

theorem rv_cons_mk {a b x xs} (ha : RValue σ a (.data x)) (hb : RValue σ b (.data (.arr xs))) :
    RValue σ (.cons a b) (.data (.arr (x :: xs))) := by
  simp only [RValue, MValue.toP, Data.toP, Data.listToP] at ha hb ⊢
  exact .cons ha hb

theorem rv_closure_mk {c e env} (he : REnv σ e env) : RValue σ (.closure c e) (.closure c env) := by
  simp only [RValue, MValue.toP]
  exact .closure he

theorem re_cons_mk {a b v vs} (ha : RValue σ a v) (hb : REnv σ b vs) :
    REnv σ (.cons a b) (v :: vs) := by
  simp only [REnv, envToP]
  exact .cons ha hb

theorem rv_data_mk (d : Data) : RValue σ d.toP (.data d) := by
  simpa [RValue, MValue.toP] using unf_data σ d

theorem rv_list_mk (xs : List Data) : RValue σ (Data.listToP xs) (.data (.arr xs)) := by
  simpa [RValue, MValue.toP, Data.toP] using unf_list σ xs

theorem toData_unf : ∀ (x : P R) {d q}, x.toData = some d → Unf σ x q → q = d.toP
  | .nat n, _, _, h, hu => by cases hu; simp [P.toData] at h; simp [← h, Data.toP]
  | .name n, _, _, h, hu => by cases hu; simp [P.toData] at h; simp [← h, Data.toP]
  | .text t, _, _, h, hu => by cases hu; simp [P.toData] at h; simp [← h, Data.toP]
  | .nil, _, _, h, hu => by cases hu; simp [P.toData] at h; simp [← h, Data.toP, Data.listToP]
  | .cons a b, _, _, h, hu => by
    cases hu with
    | cons ha hb =>
      simp only [P.toData] at h
      cases h1 : a.toData with
      | none => simp [h1] at h
      | some x =>
        cases h2 : b.toData with
        | none => simp [h1, h2] at h
        | some y =>
          cases y with
          | nat m => simp [h1, h2] at h
          | name m => simp [h1, h2] at h
          | text t => simp [h1, h2] at h
          | arr xs =>
            simp [h1, h2] at h
            have e1 := toData_unf a h1 ha
            have e2 := toData_unf b h2 hb
            simp [← h, Data.toP, Data.listToP, e1, e2]
  | .closure c e, _, _, h, _ => by simp [P.toData] at h
  | .ref r, _, _, h, _ => by simp [P.toData] at h

theorem toP_data {v : MValue} {d : Data} (h : (v.toP : P R) = d.toP) : v = .data d := by
  cases v with
  | closure c env => exact absurd h.symm (by simpa [MValue.toP] using Data.toP_ne_closure)
  | data d' => simp only [MValue.toP] at h; rw [Data.toP_inj h]

end Inversion

/-! ## The lazy machine reaches every state of the plain machine -/

/-- After one or more lazy steps, a state that resolves to `t`. -/
def Reaches (σ : Store R) (ps : PState R) (t : State) : Prop :=
  ∃ k ps', lrun σ (k + 1) ps = .at ps' ∧ RState σ ps' t

variable {σ : Store R}

theorem Reaches.real {ps ps' : PState R} {t} (h : lstep σ ps = .next ps') (hr : RState σ ps' t) :
    Reaches σ ps t :=
  ⟨0, ps', by simp [lrun, h], hr⟩

theorem Reaches.later {ps ps1 : PState R} {t} (h : lstep σ ps = .next ps1)
    (hg : Reaches σ ps1 t) : Reaches σ ps t := by
  obtain ⟨k, ps', hk, hr⟩ := hg
  exact ⟨k + 1, ps', by rw [lrun, h]; exact hk, hr⟩

omit [Ops] in
theorem re_nil_mk : REnv σ .nil [] := by
  simpa [REnv, envToP] using (Unf.nil : Unf σ .nil .nil)

omit [Ops] in
theorem fetch_some {r : R} {p} {f : P R → PState R} (h : σ r = some p) :
    fetch σ r f = .next (f p) := by
  simp [fetch, h]

/-- Fetch at one place until what is there is not a reference. -/
theorem force {F : P R → PState R} {t : State}
    (hf : ∀ r, lstep σ (F (.ref r)) = fetch σ r F) {p q : P R} (h : Unf σ p q) :
    (∀ p', (∀ r, p' ≠ .ref r) → Unf σ p' q → Reaches σ (F p') t) → Reaches σ (F p) t := by
  induction h with
  | nat => intro hh; exact hh _ (by intro r h; cases h) .nat
  | name => intro hh; exact hh _ (by intro r h; cases h) .name
  | text => intro hh; exact hh _ (by intro r h; cases h) .text
  | nil => intro hh; exact hh _ (by intro r h; cases h) .nil
  | cons a b _ _ => intro hh; exact hh _ (by intro r h; cases h) (.cons a b)
  | closure a _ => intro hh; exact hh _ (by intro r h; cases h) (.closure a)
  | ref hr _ ih => intro hh; exact .later ((hf _).trans (fetch_some hr)) (ih hh)

abbrev RFrames (σ : Store R) := All2 (fun (f : PFrame R) (m : Frame) => f.code = m.code ∧ REnv σ f.env m.env)

theorem step_access_some {j k} {menv : MEnv} {m mstk mfrs} (h : menv[j]? = some m) :
    step (.running (.access j k) menv mstk mfrs) = .running k menv (m :: mstk) mfrs := by
  simp [step, h]

theorem step_access_none {j k} {menv : MEnv} {mstk mfrs} (h : menv[j]? = none) :
    step (.running (.access j k) menv mstk mfrs) = .halted (.unbound j) := by
  simp [step, h]

theorem seek {j k} {e : P R} {menv stk mstk frs mfrs} (he : REnv σ e menv)
    (hs : All2 (RValue σ) stk mstk) (hf : RFrames σ frs mfrs) :
    ∀ i cur suffix, REnv σ cur suffix → suffix[i]? = menv[j]? →
      Reaches σ (.seeking j i cur k e stk frs) (step (.running (.access j k) menv mstk mfrs)) := by
  intro i
  induction i with
  | zero =>
    intro cur suffix hc hi
    refine force (F := fun p => .seeking j 0 p k e stk frs) (fun r => rfl) hc ?_
    intro p' hp hu
    cases p' with
    | ref r => exact absurd rfl (hp r)
    | nat n => exact (re_nat hu).elim
    | name n => exact (re_name hu).elim
    | text t => exact (re_text hu).elim
    | closure c e' => exact (re_closure hu).elim
    | nil =>
      have := re_nil hu; subst this
      rw [step_access_none (by simpa using hi.symm)]
      exact .real rfl (.halted .unbound)
    | cons v t =>
      obtain ⟨m, ms, rfl, hv, _⟩ := re_cons hu
      rw [step_access_some (by simpa using hi.symm)]
      exact .real rfl (.running he (.cons hv hs) hf)
  | succ i ih =>
    intro cur suffix hc hi
    refine force (F := fun p => .seeking j (i + 1) p k e stk frs) (fun r => rfl) hc ?_
    intro p' hp hu
    cases p' with
    | ref r => exact absurd rfl (hp r)
    | nat n => exact (re_nat hu).elim
    | name n => exact (re_name hu).elim
    | text t => exact (re_text hu).elim
    | closure c e' => exact (re_closure hu).elim
    | nil =>
      have := re_nil hu; subst this
      rw [step_access_none (by simpa using hi.symm)]
      exact .real rfl (.halted .unbound)
    | cons v t =>
      obtain ⟨m, ms, rfl, _, ht⟩ := re_cons hu
      exact .later rfl (ih t ms ht (by simpa using hi))


theorem prim_top {k n} {e : P R} {menv stk mstk frs mfrs} (he : REnv σ e menv)
    (hs : All2 (RValue σ) stk mstk) (hf : RFrames σ frs mfrs) {vx : MValue} :
    ∀ d x, UnfD σ d x vx.toP →
      Reaches σ (.running (.prim k) e (x :: .nat n :: stk) frs)
        (step (.running (.prim k) menv (vx :: .data (.nat n) :: mstk) mfrs)) := by
  intro d
  induction d with
  | zero =>
    intro x hx
    by_cases hc : ∀ b cap, x ≠ .closure b cap
    · have hl := lPrim_nat σ k e x n stk frs hc
      cases hd : x.toData with
      | some d0 =>
        have := toP_data (toData_unf x hd hx.unf); subst this
        exact .real (by show lPrim σ k e _ frs = _; rw [hl, hd])
          (.running he (.cons (rv_data_mk _) hs) hf)
      | none =>
        have hxe := hx.zero rfl
        subst hxe
        cases vx with
        | closure b cenv => exact absurd rfl (hc b (envToP cenv))
        | data d0 => simp [MValue.toP, toData_toP] at hd
    · cases x with
      | closure b cap =>
        obtain ⟨cenv, rfl, _⟩ := rv_closure hx.unf
        exact .real rfl (.halted .wrong)
      | _ => exact absurd (by intro b cap h; cases h) hc
  | succ d ih =>
    intro x hx
    by_cases hc : ∀ b cap, x ≠ .closure b cap
    · have hl := lPrim_nat σ k e x n stk frs hc
      cases hd : x.toData with
      | some d0 =>
        have := toP_data (toData_unf x hd hx.unf); subst this
        exact .real (by show lPrim σ k e _ frs = _; rw [hl, hd])
          (.running he (.cons (rv_data_mk _) hs) hf)
      | none =>
        obtain ⟨x', hh, hx'⟩ := UnfD.hyd x hx
        exact .later (by show lPrim σ k e _ frs = _; rw [hl, hd]; simp only [hh]) (ih x' hx')
    · cases x with
      | closure b cap =>
        obtain ⟨cenv, rfl, _⟩ := rv_closure hx.unf
        exact .real rfl (.halted .wrong)
      | _ => exact absurd (by intro b cap h; cases h) hc

theorem prim_top_name {k n} {e : P R} {menv stk mstk frs mfrs} (he : REnv σ e menv)
    (hs : All2 (RValue σ) stk mstk) (hf : RFrames σ frs mfrs) {vx : MValue} :
    ∀ d x, UnfD σ d x vx.toP →
      Reaches σ (.running (.prim k) e (x :: .name n :: stk) frs)
        (step (.running (.prim k) menv (vx :: .data (.name n) :: mstk) mfrs)) := by
  intro d
  induction d with
  | zero =>
    intro x hx
    by_cases hc : ∀ b cap, x ≠ .closure b cap
    · have hl := lPrim_name σ k e x n stk frs hc
      cases hd : x.toData with
      | some d0 =>
        have := toP_data (toData_unf x hd hx.unf); subst this
        exact .real (by show lPrim σ k e _ frs = _; rw [hl, hd])
          (.running he (.cons (rv_data_mk _) hs) hf)
      | none =>
        have hxe := hx.zero rfl
        subst hxe
        cases vx with
        | closure b cenv => exact absurd rfl (hc b (envToP cenv))
        | data d0 => simp [MValue.toP, toData_toP] at hd
    · cases x with
      | closure b cap =>
        obtain ⟨cenv, rfl, _⟩ := rv_closure hx.unf
        exact .real rfl (.halted .wrong)
      | _ => exact absurd (by intro b cap h; cases h) hc
  | succ d ih =>
    intro x hx
    by_cases hc : ∀ b cap, x ≠ .closure b cap
    · have hl := lPrim_name σ k e x n stk frs hc
      cases hd : x.toData with
      | some d0 =>
        have := toP_data (toData_unf x hd hx.unf); subst this
        exact .real (by show lPrim σ k e _ frs = _; rw [hl, hd])
          (.running he (.cons (rv_data_mk _) hs) hf)
      | none =>
        obtain ⟨x', hh, hx'⟩ := UnfD.hyd x hx
        exact .later (by show lPrim σ k e _ frs = _; rw [hl, hd]; simp only [hh]) (ih x' hx')
    · cases x with
      | closure b cap =>
        obtain ⟨cenv, rfl, _⟩ := rv_closure hx.unf
        exact .real rfl (.halted .wrong)
      | _ => exact absurd (by intro b cap h; cases h) hc

/-- The second entry of a `cons` is known to be data; the top is forced. -/
theorem cons_top {k} {e : P R} {menv stk mstk frs mfrs} (he : REnv σ e menv)
    (hs : All2 (RValue σ) stk mstk) (hf : RFrames σ frs mfrs) {y : P R} {dy : Data}
    (hy : RValue σ y (.data dy))
    (hshape : (∃ n, y = .nat n) ∨ y = .nil ∨ (∃ a b, y = .cons a b) ∨ (∃ n, y = .name n) ∨
      ∃ t, y = .text t)
    {x : P R} {vx : MValue} (hx : RValue σ x vx) :
    Reaches σ (.running (.cons k) e (x :: y :: stk) frs)
      (step (.running (.cons k) menv (vx :: .data dy :: mstk) mfrs)) := by
  rcases hshape with ⟨n, rfl⟩ | rfl | ⟨a, b, rfl⟩ | ⟨n, rfl⟩ | ⟨t, rfl⟩ <;>
  · refine force (F := fun p => .running (.cons k) e (p :: _ :: stk) frs) (fun r => rfl) hx ?_
    intro p' hp hu
    cases p' with
    | ref r => exact absurd rfl (hp r)
    | nat m => have := rv_nat hu; subst this; exact .real rfl (.halted .wrong)
    | name m => have := rv_name hu; subst this; exact .real rfl (.halted .wrong)
    | text t' =>
      have := rv_text hu; subst this
      exact .real rfl (.running he (.cons (rv_cons_mk hy (rv_list_mk _)) hs) hf)
    | closure c e' =>
      obtain ⟨cenv, rfl, _⟩ := rv_closure hu
      exact .real rfl (.halted .wrong)
    | nil =>
      have := rv_nil hu; subst this
      exact .real rfl (.running he (.cons (rv_cons_mk hy hu) hs) hf)
    | cons a' b' =>
      obtain ⟨z, zs, rfl, _, _⟩ := rv_cons hu
      exact .real rfl (.running he (.cons (rv_cons_mk hy hu) hs) hf)

omit [Ops] in
/-- Frames pushed the same way on both sides still resolve. -/
theorem all2_push {k : Code} {e : P R} {menv : MEnv} {frs : List (PFrame R)} {mfrs : List Frame}
    (he : REnv σ e menv)
    (hf : All2 (fun (f : PFrame R) (m : Frame) => f.code = m.code ∧ REnv σ f.env m.env) frs mfrs) :
    All2 (fun (f : PFrame R) (m : Frame) => f.code = m.code ∧ REnv σ f.env m.env)
      (ppush k e frs) (push k menv mfrs) := by
  cases k <;> first | exact hf | exact .cons ⟨rfl, he⟩ hf

/-- From a state that resolves to `s`, the lazy machine with the whole store
    reaches a state that resolves to `step s`. -/
theorem progress {ps : PState R} {s : State} (h : RState σ ps s) : Reaches σ ps (step s) := by
  cases h with
  | halted ho => exact .real rfl (.halted ho)
  | fault => exact .real rfl .fault
  | @running c e menv stk mstk frs mfrs he hs hf =>
    cases c with
    | done =>
      cases hf with
      | nil =>
        cases hs with
        | nil => exact .real rfl .fault
        | cons hv ht =>
          cases ht with
          | nil => exact .real rfl (.halted (.value hv))
          | cons _ _ => exact .real rfl .fault
      | @cons fr mfr frs' mfrs' hfr hft =>
        obtain ⟨hc, hfe⟩ := hfr
        cases mfr with
        | mk mc me =>
          cases fr with
          | mk fc fe =>
            simp only at hc hfe; subst hc
            cases hs with
            | nil => exact .real rfl (.running hfe .nil hft)
            | cons hv ht =>
              cases ht with
              | nil => exact .real rfl (.running hfe (.cons hv .nil) hft)
              | cons hv2 ht2 => exact .real rfl (.running hfe (.cons hv (.cons hv2 ht2)) hft)
    | access i k => exact .later rfl (seek he hs hf i e menv he rfl)
    | closure b k => exact .real rfl (.running he (.cons (rv_closure_mk he) hs) hf)
    | literal d k => exact .real rfl (.running he (.cons (rv_data_mk d) hs) hf)
    | checkFun k =>
      cases hs with
      | nil => exact .real rfl .fault
      | @cons x vx stk' mstk' hx ht =>
        refine force (F := fun p => .running (.checkFun k) e (p :: stk') frs) (fun r => rfl) hx ?_
        intro p' hp hu
        cases p' with
        | ref r => exact absurd rfl (hp r)
        | nat m => have := rv_nat hu; subst this; exact .real rfl (.halted .wrong)
        | name m => have := rv_name hu; subst this; exact .real rfl (.halted .wrong)
        | text t => have := rv_text hu; subst this; exact .real rfl (.halted .wrong)
        | nil => have := rv_nil hu; subst this; exact .real rfl (.halted .wrong)
        | cons a b => obtain ⟨z, zs, rfl, _, _⟩ := rv_cons hu; exact .real rfl (.halted .wrong)
        | closure c e' =>
          obtain ⟨cenv, rfl, _⟩ := rv_closure hu
          exact .real rfl (.running he (.cons hu ht) hf)
    | checkData k =>
      cases hs with
      | nil => exact .real rfl .fault
      | @cons x vx stk' mstk' hx ht =>
        refine force (F := fun p => .running (.checkData k) e (p :: stk') frs) (fun r => rfl) hx ?_
        intro p' hp hu
        cases p' with
        | ref r => exact absurd rfl (hp r)
        | nat m => have := rv_nat hu; subst this; exact .real rfl (.running he (.cons hu ht) hf)
        | name m => have := rv_name hu; subst this; exact .real rfl (.running he (.cons hu ht) hf)
        | text t => have := rv_text hu; subst this; exact .real rfl (.running he (.cons hu ht) hf)
        | nil => have := rv_nil hu; subst this; exact .real rfl (.running he (.cons hu ht) hf)
        | cons a b =>
          obtain ⟨z, zs, rfl, _, _⟩ := rv_cons hu
          exact .real rfl (.running he (.cons hu ht) hf)
        | closure c e' =>
          obtain ⟨cenv, rfl, _⟩ := rv_closure hu
          exact .real rfl (.halted .wrong)
    | succ k =>
      cases hs with
      | nil => exact .real rfl .fault
      | @cons x vx stk' mstk' hx ht =>
        refine force (F := fun p => .running (.succ k) e (p :: stk') frs) (fun r => rfl) hx ?_
        intro p' hp hu
        cases p' with
        | ref r => exact absurd rfl (hp r)
        | nat m =>
          have := rv_nat hu; subst this
          exact .real rfl (.running he (.cons rv_nat_mk ht) hf)
        | name m =>
          have := rv_name hu; subst this
          exact .real rfl (.running he (.cons rv_nat_mk ht) hf)
        | text t => have := rv_text hu; subst this; exact .real rfl (.halted .wrong)
        | nil => have := rv_nil hu; subst this; exact .real rfl (.halted .wrong)
        | cons a b => obtain ⟨z, zs, rfl, _, _⟩ := rv_cons hu; exact .real rfl (.halted .wrong)
        | closure c e' =>
          obtain ⟨cenv, rfl, _⟩ := rv_closure hu
          exact .real rfl (.halted .wrong)
    | checkNat k =>
      cases hs with
      | nil => exact .real rfl .fault
      | @cons x vx stk' mstk' hx ht =>
        refine force (F := fun p => .running (.checkNat k) e (p :: stk') frs) (fun r => rfl) hx ?_
        intro p' hp hu
        cases p' with
        | ref r => exact absurd rfl (hp r)
        | nat m =>
          have := rv_nat hu; subst this
          exact .real rfl (.running he (.cons hu ht) hf)
        | name m =>
          have := rv_name hu; subst this
          exact .real rfl (.running he (.cons hu ht) hf)
        | text t => have := rv_text hu; subst this; exact .real rfl (.halted .wrong)
        | nil => have := rv_nil hu; subst this; exact .real rfl (.halted .wrong)
        | cons a b => obtain ⟨z, zs, rfl, _, _⟩ := rv_cons hu; exact .real rfl (.halted .wrong)
        | closure c e' =>
          obtain ⟨cenv, rfl, _⟩ := rv_closure hu
          exact .real rfl (.halted .wrong)
    | dcase z sc nb cb k =>
      cases hs with
      | nil => exact .real rfl .fault
      | @cons x vx stk' mstk' hx ht =>
        refine force (F := fun p => .running (.dcase z sc nb cb k) e (p :: stk') frs)
          (fun r => rfl) hx ?_
        intro p' hp hu
        cases p' with
        | ref r => exact absurd rfl (hp r)
        | nat m =>
          have := rv_nat hu; subst this
          cases m with
          | zero => exact .real rfl (.running he ht (all2_push he hf))
          | succ m =>
            exact .real rfl (.running (re_cons_mk rv_nat_mk he) ht (all2_push he hf))
        | name m =>
          have := rv_name hu; subst this
          cases m with
          | zero => exact .real rfl (.running he ht (all2_push he hf))
          | succ m =>
            exact .real rfl (.running (re_cons_mk rv_nat_mk he) ht (all2_push he hf))
        | text t =>
          have := rv_text hu; subst this
          cases t with
          | nil => exact .real rfl (.running he ht (all2_push he hf))
          | cons ch r =>
            exact .real rfl
              (.running (re_cons_mk rv_text_mk (re_cons_mk rv_nat_mk he)) ht (all2_push he hf))
        | nil =>
          have := rv_nil hu; subst this
          exact .real rfl (.running he ht (all2_push he hf))
        | cons a b =>
          obtain ⟨y, ys, rfl, ha, hb⟩ := rv_cons hu
          exact .real rfl (.running (re_cons_mk hb (re_cons_mk ha he)) ht (all2_push he hf))
        | closure c e' =>
          obtain ⟨cenv, rfl, _⟩ := rv_closure hu
          exact .real rfl (.halted .wrong)
    | apply k =>
      cases hs with
      | nil => exact .real rfl .fault
      | @cons a va stk1 mstk1 ha ht1 =>
        cases ht1 with
        | nil => exact .real rfl .fault
        | @cons y vy stk' mstk' hy ht =>
          refine force (F := fun p => .running (.apply k) e (a :: p :: stk') frs)
            (fun r => rfl) hy ?_
          intro p' hp hu
          cases p' with
          | ref r => exact absurd rfl (hp r)
          | nat m => have := rv_nat hu; subst this; exact .real rfl .fault
          | name m => have := rv_name hu; subst this; exact .real rfl .fault
          | text t => have := rv_text hu; subst this; exact .real rfl .fault
          | nil => have := rv_nil hu; subst this; exact .real rfl .fault
          | cons a' b' => obtain ⟨z, zs, rfl, _, _⟩ := rv_cons hu; exact .real rfl .fault
          | closure c e' =>
            obtain ⟨cenv, rfl, hce⟩ := rv_closure hu
            exact .real rfl (.running (re_cons_mk ha hce) ht (all2_push he hf))
    | cons k =>
      cases hs with
      | nil => exact .real rfl .fault
      | @cons x vx stk1 mstk1 hx ht1 =>
        cases ht1 with
        | nil => exact .real (by cases x <;> rfl) (by cases vx with | closure _ _ => exact .fault | data d => cases d <;> exact .fault)
        | @cons y vy stk' mstk' hy ht =>
          refine force (F := fun p => .running (.cons k) e (x :: p :: stk') frs)
            (fun r => by cases x <;> rfl) hy ?_
          intro p' hp hu
          cases p' with
          | ref r => exact absurd rfl (hp r)
          | nat m =>
            have := rv_nat hu; subst this
            exact cons_top he ht hf hu (.inl ⟨m, rfl⟩) hx
          | nil =>
            have := rv_nil hu; subst this
            exact cons_top he ht hf hu (.inr (.inl rfl)) hx
          | cons a' b' =>
            obtain ⟨z, zs, rfl, _, _⟩ := rv_cons hu
            exact cons_top he ht hf hu (.inr (.inr (.inl ⟨a', b', rfl⟩))) hx
          | name m =>
            have := rv_name hu; subst this
            exact cons_top he ht hf hu (.inr (.inr (.inr (.inl ⟨m, rfl⟩)))) hx
          | text t =>
            have := rv_text hu; subst this
            exact cons_top he ht hf hu (.inr (.inr (.inr (.inr ⟨t, rfl⟩)))) hx
          | closure c e' =>
            obtain ⟨cenv, rfl, _⟩ := rv_closure hu
            exact .real (by cases x <;> rfl) (by cases vx with | closure _ _ => exact .fault | data d => cases d <;> exact .fault)
    | prim k =>
      cases hs with
      | nil => exact .real rfl .fault
      | @cons x vx stk1 mstk1 hx ht1 =>
        cases ht1 with
        | nil => exact .real (by cases x <;> rfl) (by cases vx <;> exact .fault)
        | @cons y vy stk' mstk' hy ht =>
          refine force (F := fun p => .running (.prim k) e (x :: p :: stk') frs)
            (fun r => by cases x <;> rfl) hy ?_
          intro p' hp hu
          cases p' with
          | ref r => exact absurd rfl (hp r)
          | nat m =>
            have := rv_nat hu; subst this
            obtain ⟨d, hd⟩ := Unf.depth hx
            exact prim_top he ht hf d x hd
          | name m =>
            have := rv_name hu; subst this
            obtain ⟨d, hd⟩ := Unf.depth hx
            exact prim_top_name he ht hf d x hd
          | text t =>
            have := rv_text hu; subst this
            exact .real (by cases x <;> rfl) (by cases vx <;> exact .fault)
          | nil =>
            have := rv_nil hu; subst this
            exact .real (by cases x <;> rfl) (by cases vx <;> exact .fault)
          | cons a' b' =>
            obtain ⟨z, zs, rfl, _, _⟩ := rv_cons hu
            exact .real (by cases x <;> rfl) (by cases vx <;> exact .fault)
          | closure c e' =>
            obtain ⟨cenv, rfl, _⟩ := rv_closure hu
            exact .real (by cases x <;> rfl) (by cases vx <;> exact .fault)


/-! ## Runs -/

omit [Ops] in
theorem all2_mono {α β : Type} {r r' : α → β → Prop} (h : ∀ a b, r a b → r' a b) {as bs}
    (ha : All2 r as bs) : All2 r' as bs := by
  induction ha with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (h _ _ hab) ih

omit [Ops] in
/-- A state that resolves under a store resolves under any store that holds more. -/
theorem RState.mono {σ τ : Store R} (hle : σ.le τ) {ps s} (h : RState σ ps s) : RState τ ps s := by
  cases h with
  | running he hs hf =>
    exact .running (Unf.mono hle he) (all2_mono (fun _ _ h => Unf.mono hle h) hs)
      (all2_mono (fun _ _ h => ⟨h.1, Unf.mono hle h.2⟩) hf)
  | halted ho =>
    cases ho with
    | value hv => exact .halted (.value (Unf.mono hle hv))
    | unbound => exact .halted .unbound
    | wrong => exact .halted .wrong
  | fault => exact .fault

omit [Ops] in
/-- Saving with no cut: a state held whole resolves to itself, under any store. -/
theorem saved_resolves (σ : Store R) : ∀ s : State, RState σ s.toP s
  | .running c env stk frs => by
    refine .running (unf_env σ env) ?_ ?_
    · induction stk with
      | nil => exact .nil
      | cons v vs ih => exact .cons (unf_value σ v) ih
    · induction frs with
      | nil => exact .nil
      | cons f fs ih => exact .cons ⟨rfl, unf_env σ f.env⟩ ih
  | .halted (.value v) => .halted (.value (unf_value σ v))
  | .halted (.unbound _) => .halted .unbound
  | .halted .wrong => .halted .wrong
  | .fault => .fault

omit [Ops] in
/-- A cut: a piece put in the store under `r` can be replaced by `ref r`. -/
theorem cut_resolves {r : R} {p q : P R} (hr : σ r = some p) (h : Unf σ p q) :
    Unf σ (.ref r) q := .ref hr h

omit [Ops] in
mutual
  theorem MValue.toP_inj : ∀ (v : MValue) {w : MValue}, (v.toP : P R) = w.toP → v = w
    | .closure c env, w, h => by
      obtain ⟨env', rfl, he⟩ := toP_closure (R := R) (v := w) (by simpa [MValue.toP] using h.symm)
      rw [envToP_inj env he]
    | .data d, w, h => (toP_data (by simpa [MValue.toP] using h.symm)).symm
  theorem envToP_inj : ∀ (vs : List MValue) {ws : List MValue},
      (envToP vs : P R) = envToP ws → vs = ws
    | [], ws, h => (envToP_nil (by simpa [envToP] using h.symm)).symm
    | v :: vs, ws, h => by
      obtain ⟨w, ws', rfl, hv, hvs⟩ := envToP_cons (R := R) (env := ws)
        (by simpa [envToP] using h.symm)
      rw [MValue.toP_inj v hv, envToP_inj vs hvs]
end

omit [Ops] in
/-- A partial outcome resolves to at most one outcome. -/
theorem resolve_unique {po : POutcome R} {o o' : MOutcome} (h : ROutcome σ po o)
    (h' : ROutcome σ po o') : o = o' := by
  cases h with
  | value hv => cases h' with | value hv' => rw [MValue.toP_inj _ (Unf.unique hv hv')]
  | unbound => cases h'; rfl
  | wrong => cases h'; rfl

theorem lrun_add (σ : Store R) : ∀ j n (ps ps' : PState R), lrun σ j ps = .at ps' →
    lrun σ (j + n) ps = lrun σ n ps' := by
  intro j
  induction j with
  | zero => intro n ps ps' h; simp [lrun] at h; simp [h]
  | succ j ih =>
    intro n ps ps' h
    rw [show j + 1 + n = (j + n) + 1 by omega]
    simp only [lrun] at h ⊢
    cases hl : lstep σ ps with
    | next s' => simp only [hl] at h ⊢; exact ih n s' ps' h
    | needs r => simp [hl] at h

theorem lrun_halted (σ : Store R) (po : POutcome R) : ∀ n, lrun σ n (.halted po) = .at (.halted po) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa [lrun, lstep] using ih

/-- For every number of steps of the plain machine, the lazy machine with the
    whole store reaches a state that resolves to the plain machine's state. -/
theorem lazy_simulates : ∀ n {ps : PState R} {s : State}, RState σ ps s →
    ∃ k ps', n ≤ k ∧ lrun σ k ps = .at ps' ∧ RState σ ps' (run n s) := by
  intro n
  induction n with
  | zero => intro ps s h; exact ⟨0, ps, Nat.le_refl _, rfl, h⟩
  | succ n ih =>
    intro ps s h
    obtain ⟨k1, ps1, h1, hr1⟩ := progress h
    obtain ⟨k2, ps2, hk, h2, hr2⟩ := ih hr1
    exact ⟨k1 + 1 + k2, ps2, by omega, by rw [lrun_add σ _ _ _ _ h1]; exact h2, hr2⟩

/-- What the plain machine halts with, the lazy machine halts with. -/
theorem lazy_complete {ps : PState R} {s : State} (h : RState σ ps s) {n o}
    (hr : run n s = .halted o) :
    ∃ k po, lrun σ k ps = .at (.halted po) ∧ ROutcome σ po o := by
  obtain ⟨k, ps', _, hk, hrs⟩ := lazy_simulates n h
  rw [hr] at hrs
  cases hrs with
  | halted ho => exact ⟨k, _, hk, ho⟩

theorem lrun_mono {σ τ : Store R} (hle : σ.le τ) : ∀ k {ps ps' : PState R},
    lrun σ k ps = .at ps' → lrun τ k ps = .at ps' := by
  intro k
  induction k with
  | zero => intro ps ps' h; exact h
  | succ k ih =>
    intro ps ps' h
    simp only [lrun] at h ⊢
    cases hl : lstep σ ps with
    | next s' => simp only [hl] at h; simp only [lstep_mono hle hl]; exact ih h
    | needs r => simp [hl] at h

/-- A missing piece is a pause, never a different result: what the lazy machine
    halts with under part of a store is what the plain machine halts with. -/
theorem lazy_sound {σ' : Store R} (hle : σ'.le σ) {ps : PState R} {s : State}
    (h : RState σ ps s) {k po} (hl : lrun σ' k ps = .at (.halted po)) :
    ∃ o, run k s = .halted o ∧ ROutcome σ po o := by
  have hl' := lrun_mono hle k hl
  obtain ⟨k', ps', hk, hk', hrs⟩ := lazy_simulates k h
  have : lrun σ k' ps = .at (.halted po) := by
    rw [show k' = k + (k' - k) by omega, lrun_add σ _ _ _ _ hl', lrun_halted]
  rw [this] at hk'
  cases hk'
  generalize run k s = t at hrs
  cases hrs with
  | halted ho => exact ⟨_, rfl, ho⟩

theorem lrun_paused {σ : Store R} : ∀ k {ps ps' : PState R} {r : R},
    lrun σ k ps = .paused r ps' → σ r = none ∧ ∃ j, j < k ∧ lrun σ j ps = .at ps' := by
  intro k
  induction k with
  | zero => intro ps ps' r h; simp [lrun] at h
  | succ k ih =>
    intro ps ps' r h
    simp only [lrun] at h
    cases hl : lstep σ ps with
    | next s' =>
      simp only [hl] at h
      obtain ⟨hn, j, hj, hat⟩ := ih h
      exact ⟨hn, j + 1, by omega, by simp only [lrun, hl]; exact hat⟩
    | needs r' =>
      simp only [hl] at h
      cases h
      exact ⟨lstep_needs hl, 0, by omega, rfl⟩

/-- A run pauses only on a reference the store lacks, and under any store that
    holds more, the run from the start passes through the paused state. -/
theorem lazy_pause {σ' τ : Store R} (hle : σ'.le τ) {k} {ps ps' : PState R} {r : R}
    (h : lrun σ' k ps = .paused r ps') :
    σ' r = none ∧ ∃ j, j < k ∧ ∀ n, lrun τ (j + n) ps = lrun τ n ps' := by
  obtain ⟨hn, j, hj, hat⟩ := lrun_paused k h
  exact ⟨hn, j, hj, fun n => lrun_add τ _ _ _ _ (lrun_mono hle j hat)⟩

omit [Ops] in
theorem Store.le_union_left (σ τ : Store R) : σ.le (σ.union τ) := by
  intro r p h; simp [Store.union, h]

omit [Ops] in
theorem Store.le_union_right {σ τ : Store R} (hc : σ.Compatible τ) : τ.le (σ.union τ) := by
  intro r q h
  unfold Store.union
  cases hs : σ r with
  | none => simpa using h
  | some p => simp [hc r p q hs h]

/-- Two stores that agree wherever both hold a piece give the same result. -/
theorem lazy_agree {σ₁ σ₂ : Store R} (hc : σ₁.Compatible σ₂) {ps : PState R} {k₁ k₂ po₁ po₂}
    (h₁ : lrun σ₁ k₁ ps = .at (.halted po₁)) (h₂ : lrun σ₂ k₂ ps = .at (.halted po₂)) :
    po₁ = po₂ := by
  have a := lrun_mono (Store.le_union_left σ₁ σ₂) k₁ h₁
  have b := lrun_mono (Store.le_union_right hc) k₂ h₂
  have a' := lrun_add _ k₁ k₂ _ _ a
  have b' := lrun_add _ k₂ k₁ _ _ b
  rw [lrun_halted] at a' b'
  rw [Nat.add_comm, b'] at a'
  cases a'; rfl

/-- A program run from the store: the lazy machine halts with what direct
    evaluation gives. -/
theorem lazy_program (σ : Store R) (t : Term) (o : Outcome) :
    Direct [] t o ↔
    ∃ k po w, lrun σ k (.running (compile t) .nil [] []) = .at (.halted po) ∧
      ROutcome σ po w ∧ readOutcome w = some o := by
  have hinit : RState σ (.running (compile t) .nil [] []) (load (compile t)) :=
    .running re_nil_mk .nil .nil
  rw [machine_correct]
  constructor
  · rintro ⟨n, w, hr, hw⟩
    obtain ⟨k, po, hk, ho⟩ := lazy_complete hinit hr
    exact ⟨k, po, w, hk, ho, hw⟩
  · rintro ⟨k, po, w, hk, ho, hw⟩
    obtain ⟨w', hr, ho'⟩ := lazy_sound (fun _ _ h => h) hinit hk
    have := resolve_unique ho ho'
    subst this
    exact ⟨k, w, hr, hw⟩

/-- A turn of the request driver run from a stored continuation: what the
    plain machine gives, the lazy machine gives. -/
theorem lazy_turn_complete {pc : P R} {c : MValue} (hc : RValue σ pc c) {t : Term} {w : MOutcome}
    (h : machine.eval c t w) :
    ∃ k po, lrun σ k (.running (compile t) (.cons pc .nil) [] []) = .at (.halted po) ∧
      ROutcome σ po w := by
  obtain ⟨n, hn⟩ := h
  exact lazy_complete (.running (re_cons_mk hc re_nil_mk) .nil .nil) hn

/-- And what the lazy machine gives, under any part of the store, is a turn of
    the plain machine. -/
theorem lazy_turn_sound {σ' : Store R} (hle : σ'.le σ) {pc : P R} {c : MValue}
    (hc : RValue σ pc c) {t : Term} {k po}
    (h : lrun σ' k (.running (compile t) (.cons pc .nil) [] []) = .at (.halted po)) :
    ∃ w, machine.eval c t w ∧ ROutcome σ po w := by
  obtain ⟨w, hr, ho⟩ := lazy_sound hle (.running (re_cons_mk hc re_nil_mk) .nil .nil) h
  exact ⟨w, ⟨k, hr⟩, ho⟩

end Reflect
