import Circular.Representation

namespace Circular

/-- Closing substitution for closed replacement terms. Indices beneath the
    indicated number of binders are left alone. -/
def plug (env : List Term) (depth : Nat) : Term → Term
  | .var i => if i < depth then .var i else (env[i - depth]?).getD (.var i)
  | .lam b => .lam (plug env (depth + 1) b)
  | .app f a => .app (plug env depth f) (plug env depth a)
  | .quote t => .quote t

def ClosedTerms (env : List Term) : Prop := ∀ t ∈ env, Closed t

theorem scoped_mono (h : Scoped n t) (hn : n ≤ m) : Scoped m t := by
  induction t generalizing n m with
  | var => exact Nat.lt_of_lt_of_le h hn
  | lam _ ih => exact ih h (by omega)
  | app _ _ ihf iha => exact ⟨ihf h.1 hn, iha h.2 hn⟩
  | quote => trivial

theorem plug_scoped_id (h : Scoped d t) : plug env d t = t := by
  induction t generalizing d with
  | var i => change i < d at h; simp [plug, h]
  | lam _ ih => simp only [plug, ih h]
  | app _ _ ihf iha => simp only [plug, ihf h.1, iha h.2]
  | quote => rfl

theorem plug_closed_id (h : Closed t) : plug env d t = t :=
  plug_scoped_id (scoped_mono h (Nat.zero_le d))

theorem plug_eq_closeTerm (he : ClosedTerms env) : plug env d t = closeTerm env d t := by
  induction t generalizing d with
  | var i =>
    simp only [plug, closeTerm]
    split
    · rfl
    · cases hv : env[i - d]? with
      | none => rfl
      | some v =>
        simp only [Option.getD_some]
        exact (shift_eq_self_of_scoped (he v (List.mem_of_getElem? hv))).symm
  | lam _ ih => simp only [plug, closeTerm, ih]
  | app _ _ ihf iha => simp only [plug, closeTerm, ihf, iha]
  | quote => rfl

theorem plug_scoped (he : ClosedTerms env) (ht : Scoped (d + env.length) t) :
    Scoped d (plug env d t) := by
  induction t generalizing d with
  | var i =>
    simp only [plug]
    split
    · assumption
    · rename_i hi
      have hi' : i - d < env.length := by change i < d + env.length at ht; omega
      rw [List.getElem?_eq_getElem hi']
      exact scoped_mono (he _ (List.getElem_mem hi')) (Nat.zero_le d)
  | lam _ ih => exact ih (by simpa [Scoped, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht)
  | app _ _ ihf iha => exact ⟨ihf ht.1, iha ht.2⟩
  | quote => trivial

theorem plug_comp (_hs : ClosedTerms s) (he : ClosedTerms env) :
    plug s d (plug env (d + s.length) t) = plug (s ++ env) d t := by
  induction t generalizing d with
  | var i =>
    simp only [plug]
    by_cases hi : i < d
    · simp [hi, show i < d + s.length by omega, plug]
    · by_cases hs' : i - d < s.length
      · have hi' : i < d + s.length := by omega
        simp [hi', plug, hi, List.getElem?_append, hs']
      · have hi' : ¬ i < d + s.length := by omega
        simp only [ite_eq_right hi', ite_eq_right hi, List.getElem?_append, ite_eq_right hs']
        have heq : i - (d + s.length) = i - d - s.length := by omega
        rw [heq]
        cases hv : env[i - d - s.length]? with
        | none => simp [plug, hi, List.getElem?_eq_none (by omega : s.length ≤ i - d)]
        | some v =>
          simp only [Option.getD_some]
          exact plug_closed_id (he v (List.mem_of_getElem? hv))
  | lam _ ih =>
    simp only [plug]
    rw [show d + s.length + 1 = d + 1 + s.length by omega, ih]
  | app _ _ ihf iha => simp only [plug, ihf, iha]
  | quote => rfl

/-- Substitution evaluation is used only as a proof device for closed
    interpreter terms. Its results are lambda syntax, not host functions. -/
inductive Beta : Term → Term → Prop where
  | lam : Beta (.lam b) (.lam b)
  | app : Beta f (.lam b) → Beta a v → Beta (plug [v] 0 b) r → Beta (.app f a) r

theorem beta_value (h : Beta t r) : ∃ b, r = .lam b := by
  induction h with
  | lam => exact ⟨_, rfl⟩
  | app _ _ _ _ _ ih => exact ih

theorem beta_deterministic (h : Beta t r) (h' : Beta t r') : r = r' := by
  induction h generalizing r' with
  | lam => cases h'; rfl
  | app _ _ _ ihf iha ihb =>
    cases h' with
    | app hf ha hb =>
      cases ihf hf
      cases iha ha
      exact ihb hb

theorem beta_closed (h : Beta t r) (ht : Closed t) : Closed r := by
  induction h with
  | lam => exact ht
  | app _ _ _ ihf iha ihb =>
    have hf := ihf ht.1
    have ha := iha ht.2
    apply ihb
    exact plug_scoped (by simpa [ClosedTerms] using ha) hf

mutual
  inductive WFValue : Value → Prop where
    | closure : Scoped (env.length + 1) b → WFEnv env → WFValue (.closure b env)
  inductive WFEnv : Env → Prop where
    | nil : WFEnv []
    | cons : WFValue v → WFEnv env → WFEnv (v :: env)
end

namespace WFEnv
 theorem lookup {i : Nat} (he : WFEnv env) (hv : env[i]? = some v) : WFValue v := by
  induction env generalizing i with
  | nil => simp at hv
  | cons hh tail ih =>
    cases he with
    | cons hh ht =>
      cases i with
      | zero => cases hv; exact hh
      | succ i => exact ih ht hv
end WFEnv

mutual
  theorem readback_closed (hv : WFValue v) : Closed (readback v) := by
    cases hv with
    | closure hb he =>
      rw [readback]
      change Scoped 1 (closeTerm _ 1 _)
      rw [← plug_eq_closeTerm (readbacks_closed he)]
      apply plug_scoped (readbacks_closed he)
      simpa [List.length_map, Nat.add_comm] using hb
  termination_by sizeOf v

  theorem readbacks_closed (he : WFEnv env) : ClosedTerms (env.map readback) := by
    cases he with
    | nil => simp [ClosedTerms]
    | cons hv ht =>
      have hh := readback_closed hv
      have ht := readbacks_closed ht
      simpa [ClosedTerms] using And.intro hh ht
  termination_by sizeOf env
end

theorem direct_beta (h : Direct env t o) (he : WFEnv env) (ht : Scoped env.length t) :
    ∃ v, o = .value v ∧ WFValue v ∧ Beta (plug (env.map readback) 0 t) (readback v) := by
  induction h with
  | @varBound env i v hv =>
    have hw := he.lookup hv
    refine ⟨_, rfl, hw, ?_⟩
    simp only [plug, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero,
      List.getElem?_map, hv, Option.map_some, Option.getD_some]
    cases v
    simpa only [readback] using (Beta.lam (b := closeTerm _ 1 _))
  | @varUnbound env i hv =>
    have hg := List.getElem?_eq_getElem ht
    rw [hv] at hg
    contradiction
  | lam =>
    refine ⟨_, rfl, .closure ht he, ?_⟩
    rw [plug, readback, ← plug_eq_closeTerm (readbacks_closed he)]
    exact .lam
  | appUnbound hf ih =>
    obtain ⟨_, heq, _⟩ := ih he ht.1
    cases heq
  | appArgUnbound hf ha ihf iha =>
    obtain ⟨_, heq, _⟩ := iha he ht.2
    cases heq
  | appValue hf ha hb ihf iha ihb =>
    obtain ⟨vf, ef, wf, bf⟩ := ihf he ht.1
    cases ef
    cases wf with
    | closure hbody hcap =>
      obtain ⟨va, ea, wa, ba⟩ := iha he ht.2
      cases ea
      obtain ⟨v, eo, wo, bo⟩ := ihb (.cons wa hcap) (by simpa using hbody)
      rw [readback, ← plug_eq_closeTerm (readbacks_closed hcap)] at bf
      refine ⟨v, eo, wo, .app bf ba ?_⟩
      simpa using (plug_comp (s := [readback _]) (env := _) (d := 0)
        (by simpa [ClosedTerms] using readback_closed wa) (readbacks_closed hcap)) ▸ bo

/-- Reflection back into closures; the result is existential because closures
    with unused captured entries can have the same readback. -/
theorem beta_direct (h : Beta s r) :
    ∀ env t, WFEnv env → Scoped env.length t → plug (env.map readback) 0 t = s →
    ∃ v, Direct env t (.value v) ∧ WFValue v ∧ readback v = r := by
  induction h with
  | @lam b =>
    intro env t he ht eq
    cases t with
    | var i =>
      have hi : i < env.length := ht
      have hv := List.getElem?_eq_getElem hi
      have hw := he.lookup hv
      refine ⟨env[i], .varBound hv, hw, ?_⟩
      simpa [plug, List.getElem?_map, hv] using eq
    | lam c =>
      refine ⟨_, .lam, .closure ht he, ?_⟩
      simpa only [readback, ← plug_eq_closeTerm (readbacks_closed he), plug] using eq
    | app f a => simp [plug] at eq
    | quote t => simp [plug] at eq
  | @app f b a v r hf ha hb ihf iha ihb =>
    intro env t he ht eq
    cases t with
    | var i =>
      have hi : i < env.length := ht
      have hv := List.getElem?_eq_getElem hi
      have hw := he.lookup hv
      simp only [plug, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero,
        List.getElem?_map, hv, Option.map_some, Option.getD_some] at eq
      generalize env[i] = vi at eq
      cases vi
      simp [readback] at eq
    | lam c => simp [plug] at eq
    | quote t => simp [plug] at eq
    | app ft argt =>
      simp only [plug, Term.app.injEq] at eq
      obtain ⟨vf, hdf, hwf, erf⟩ := ihf env ft he ht.1 eq.1
      cases vf with
      | closure body cap =>
        cases hwf with
        | closure hbody hcap =>
          obtain ⟨va, hda, hwa, era⟩ := iha env argt he ht.2 eq.2
          have eqb : plug ((va :: cap).map readback) 0 body = plug [v] 0 b := by
            rw [readback] at erf
            rw [← plug_eq_closeTerm (readbacks_closed hcap)] at erf
            cases erf
            rw [← era]
            simpa using (plug_comp (s := [readback va]) (env := cap.map readback)
              (d := 0) (t := body) (by simpa [ClosedTerms] using readback_closed hwa)
              (readbacks_closed hcap)).symm
          obtain ⟨vr, hdr, hwr, err⟩ := ihb (va :: cap) body (.cons hwa hcap)
            (by simpa using hbody) eqb
          exact ⟨vr, .appValue hdf hda hdr, hwr, err⟩

theorem beta_direct_closed (h : Beta t r) (ht : Closed t) :
    ∃ v, Direct [] t (.value v) ∧ readback v = r := by
  obtain ⟨v, hd, _, hr⟩ := beta_direct h [] t .nil ht (plug_closed_id ht)
  exact ⟨v, hd, hr⟩

end Circular
