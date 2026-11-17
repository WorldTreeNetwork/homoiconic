import Reflect.Semantics

namespace Reflect
variable [Ops]

theorem direct_deterministic {env : Env} {t : Term} {o o' : Outcome}
    (h : Direct env t o) (h' : Direct env t o') : o = o' := by
  induction h generalizing o' with
  | varBound hv => cases h' <;> simp_all
  | varUnbound hv => cases h' <;> simp_all
  | lam => cases h'; rfl
  | lit => cases h'; rfl
  | appFunError _ he ihf =>
    cases h' <;> (try cases ihf ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | appData _ ihf =>
    cases h' <;> (try cases ihf ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | appArgError _ _ he ihf iha =>
    cases h' <;> (try cases ihf ‹_›) <;> (try cases iha ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | appValue _ _ _ ihf iha ihb =>
    cases h' <;> (try cases ihf ‹_›) <;> (try cases iha ‹_›) <;> (try cases ihb ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | succNat _ ih =>
    cases h' <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | succArr _ ih =>
    cases h' <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | succName _ ih =>
    cases h' <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | succText _ ih =>
    cases h' <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | succClosure _ ih =>
    cases h' <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | succError _ he ih =>
    cases h' <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | consArr _ _ iha ihb =>
    cases h' <;> (try cases iha ‹_›) <;> (try cases ihb ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | consText _ _ iha ihb =>
    cases h' <;> (try cases iha ‹_›) <;> (try cases ihb ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | consHeadClosure _ iha =>
    cases h' <;> (try cases iha ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | consHeadError _ he iha =>
    cases h' <;> (try cases iha ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | consTailNat _ _ iha ihb =>
    cases h' <;> (try cases iha ‹_›) <;> (try cases ihb ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | consTailName _ _ iha ihb =>
    cases h' <;> (try cases iha ‹_›) <;> (try cases ihb ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | consTailClosure _ _ iha ihb =>
    cases h' <;> (try cases iha ‹_›) <;> (try cases ihb ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | consTailError _ _ he iha ihb =>
    cases h' <;> (try cases iha ‹_›) <;> (try cases ihb ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | caseZero _ _ ihs ih =>
    cases h' <;> (try cases ihs ‹_›) <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | caseSucc _ _ ihs ih =>
    cases h' <;> (try cases ihs ‹_›) <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | caseNameZero _ _ ihs ih =>
    cases h' <;> (try cases ihs ‹_›) <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | caseNameSucc _ _ ihs ih =>
    cases h' <;> (try cases ihs ‹_›) <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | caseNil _ _ ihs ih =>
    cases h' <;> (try cases ihs ‹_›) <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | caseCons _ _ ihs ih =>
    cases h' <;> (try cases ihs ‹_›) <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | caseTextNil _ _ ihs ih =>
    cases h' <;> (try cases ihs ‹_›) <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | caseTextCons _ _ ihs ih =>
    cases h' <;> (try cases ihs ‹_›) <;> (try cases ih ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | caseClosure _ ihs =>
    cases h' <;> (try cases ihs ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | caseError _ he ihs =>
    cases h' <;> (try cases ihs ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | primCodeError _ he ihc =>
    cases h' <;> (try cases ihc ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | primCodeArr _ ihc =>
    cases h' <;> (try cases ihc ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | primCodeText _ ihc =>
    cases h' <;> (try cases ihc ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | primCodeClosure _ ihc =>
    cases h' <;> (try cases ihc ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | primArgError _ _ he ihc ihx =>
    cases h' <;> (try cases ihc ‹_›) <;> (try cases ihx ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | primArgClosure _ _ ihc ihx =>
    cases h' <;> (try cases ihc ‹_›) <;> (try cases ihx ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | primData _ _ ihc ihx =>
    cases h' <;> (try cases ihc ‹_›) <;> (try cases ihx ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | primNameArgError _ _ he ihc ihx =>
    cases h' <;> (try cases ihc ‹_›) <;> (try cases ihx ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | primNameArgClosure _ _ ihc ihx =>
    cases h' <;> (try cases ihc ‹_›) <;> (try cases ihx ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
  | primNameData _ _ ihc ihx =>
    cases h' <;> (try cases ihc ‹_›) <;> (try cases ihx ‹_›) <;> first | rfl | simp_all [Outcome.IsError]
theorem evalFuel_sound {n : Nat} {env : Env} {t : Term} {o : Outcome}
    (h : evalFuel n env t = some o) : Direct env t o := by
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
    | lit d => cases h; exact .lit
    | app f a =>
      simp only [evalFuel] at h
      repeat' split at h
      all_goals (try (simp only [Option.some.injEq] at h; subst h))
      all_goals first
        | contradiction
        | exact .appValue (ih ‹_›) (ih ‹_›) (ih h)
        | exact .appArgError (ih ‹_›) (ih ‹_›) (by simp [Outcome.IsError])
        | exact .appFunError (ih ‹_›) (by simp [Outcome.IsError])
        | exact .appData (ih ‹_›)
    | succ t =>
      simp only [evalFuel] at h
      repeat' split at h
      all_goals (try (simp only [Option.some.injEq] at h; subst h))
      all_goals first
        | contradiction
        | exact .succNat (ih ‹_›)
        | exact .succArr (ih ‹_›)
        | exact .succName (ih ‹_›)
        | exact .succText (ih ‹_›)
        | exact .succClosure (ih ‹_›)
        | exact .succError (ih ‹_›) (by simp [Outcome.IsError])
    | cons a b =>
      simp only [evalFuel] at h
      repeat' split at h
      all_goals (try (simp only [Option.some.injEq] at h; subst h))
      all_goals first
        | contradiction
        | exact .consArr (ih ‹_›) (ih ‹_›)
        | exact .consText (ih ‹_›) (ih ‹_›)
        | exact .consHeadClosure (ih ‹_›)
        | exact .consHeadError (ih ‹_›) (by simp [Outcome.IsError])
        | exact .consTailNat (ih ‹_›) (ih ‹_›)
        | exact .consTailName (ih ‹_›) (ih ‹_›)
        | exact .consTailClosure (ih ‹_›) (ih ‹_›)
        | exact .consTailError (ih ‹_›) (ih ‹_›) (by simp [Outcome.IsError])
    | dcase s z sc ni c =>
      simp only [evalFuel] at h
      repeat' split at h
      all_goals (try (simp only [Option.some.injEq] at h; subst h))
      all_goals first
        | contradiction
        | exact .caseZero (ih ‹_›) (ih h)
        | exact .caseSucc (ih ‹_›) (ih h)
        | exact .caseNameZero (ih ‹_›) (ih h)
        | exact .caseNameSucc (ih ‹_›) (ih h)
        | exact .caseNil (ih ‹_›) (ih h)
        | exact .caseCons (ih ‹_›) (ih h)
        | exact .caseTextNil (ih ‹_›) (ih h)
        | exact .caseTextCons (ih ‹_›) (ih h)
        | exact .caseClosure (ih ‹_›)
        | exact .caseError (ih ‹_›) (by simp [Outcome.IsError])
    | prim c x =>
      simp only [evalFuel] at h
      repeat' split at h
      all_goals (try (simp only [Option.some.injEq] at h; subst h))
      all_goals first
        | contradiction
        | exact .primData (ih ‹_›) (ih ‹_›)
        | exact .primArgClosure (ih ‹_›) (ih ‹_›)
        | exact .primArgError (ih ‹_›) (ih ‹_›) (by simp [Outcome.IsError])
        | exact .primNameData (ih ‹_›) (ih ‹_›)
        | exact .primNameArgClosure (ih ‹_›) (ih ‹_›)
        | exact .primNameArgError (ih ‹_›) (ih ‹_›) (by simp [Outcome.IsError])
        | exact .primCodeArr (ih ‹_›)
        | exact .primCodeText (ih ‹_›)
        | exact .primCodeClosure (ih ‹_›)
        | exact .primCodeError (ih ‹_›) (by simp [Outcome.IsError])
theorem evalFuel_mono {n m : Nat} {env : Env} {t : Term} {o : Outcome}
    (h : evalFuel n env t = some o) (hle : n ≤ m) : evalFuel m env t = some o := by
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
      | lit d => exact h
      | app f a =>
        simp only [evalFuel] at h ⊢
        repeat' split at h
        all_goals (try (simp only [Option.some.injEq] at h; subst h))
        all_goals simp_all
      | succ t =>
        simp only [evalFuel] at h ⊢
        repeat' split at h
        all_goals (try (simp only [Option.some.injEq] at h; subst h))
        all_goals simp_all
      | cons a b =>
        simp only [evalFuel] at h ⊢
        repeat' split at h
        all_goals (try (simp only [Option.some.injEq] at h; subst h))
        all_goals simp_all
      | dcase s z sc ni c =>
        simp only [evalFuel] at h ⊢
        repeat' split at h
        all_goals (try (simp only [Option.some.injEq] at h; subst h))
        all_goals simp_all
      | prim c x =>
        simp only [evalFuel] at h ⊢
        repeat' split at h
        all_goals (try (simp only [Option.some.injEq] at h; subst h))
        all_goals simp_all

theorem evalFuel_complete {env : Env} {t : Term} {o : Outcome}
    (h : Direct env t o) : ∃ n, evalFuel n env t = some o := by
  induction h with
  | varBound hv => exact ⟨1, by simp [evalFuel, hv]⟩
  | varUnbound hv => exact ⟨1, by simp [evalFuel, hv]⟩
  | lam => exact ⟨1, rfl⟩
  | lit => exact ⟨1, rfl⟩
  | @appFunError _ _ e _ _ he ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    cases e <;> simp_all [evalFuel, Outcome.IsError]
  | appData _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, hn]⟩
  | @appArgError _ _ _ _ _ e _ _ he ihf iha =>
    obtain ⟨n1, h1⟩ := ihf
    obtain ⟨n2, h2⟩ := iha
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    refine ⟨n1 + n2 + 1, ?_⟩
    cases e <;> simp_all [evalFuel, Outcome.IsError]
  | appValue _ _ _ ihf iha ihb =>
    obtain ⟨n1, h1⟩ := ihf
    obtain ⟨n2, h2⟩ := iha
    obtain ⟨n3, h3⟩ := ihb
    have h1' := evalFuel_mono h1 (m := n1 + n2 + n3) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2 + n3) (by omega)
    have h3' := evalFuel_mono h3 (m := n1 + n2 + n3) (by omega)
    exact ⟨n1 + n2 + n3 + 1, by simp [evalFuel, h1', h2', h3']⟩
  | succNat _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, hn]⟩
  | succArr _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, hn]⟩
  | succName _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, hn]⟩
  | succText _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, hn]⟩
  | succClosure _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, hn]⟩
  | @succError _ _ e _ he ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    cases e <;> simp_all [evalFuel, Outcome.IsError]
  | consArr _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | consText _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | consHeadClosure _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, hn]⟩
  | @consHeadError _ _ e _ _ he ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    cases e <;> simp_all [evalFuel, Outcome.IsError]
  | consTailNat _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | consTailName _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | consTailClosure _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | @consTailError _ _ _ _ e _ _ he iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    refine ⟨n1 + n2 + 1, ?_⟩
    cases e <;> simp_all [evalFuel, Outcome.IsError]
  | caseZero _ _ ihs ih =>
    obtain ⟨n1, h1⟩ := ihs
    obtain ⟨n2, h2⟩ := ih
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | caseSucc _ _ ihs ih =>
    obtain ⟨n1, h1⟩ := ihs
    obtain ⟨n2, h2⟩ := ih
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | caseNameZero _ _ ihs ih =>
    obtain ⟨n1, h1⟩ := ihs
    obtain ⟨n2, h2⟩ := ih
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | caseNameSucc _ _ ihs ih =>
    obtain ⟨n1, h1⟩ := ihs
    obtain ⟨n2, h2⟩ := ih
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | caseNil _ _ ihs ih =>
    obtain ⟨n1, h1⟩ := ihs
    obtain ⟨n2, h2⟩ := ih
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | caseCons _ _ ihs ih =>
    obtain ⟨n1, h1⟩ := ihs
    obtain ⟨n2, h2⟩ := ih
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | caseTextNil _ _ ihs ih =>
    obtain ⟨n1, h1⟩ := ihs
    obtain ⟨n2, h2⟩ := ih
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | caseTextCons _ _ ihs ih =>
    obtain ⟨n1, h1⟩ := ihs
    obtain ⟨n2, h2⟩ := ih
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | caseClosure _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, hn]⟩
  | @caseError _ _ e _ _ _ _ _ he ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    cases e <;> simp_all [evalFuel, Outcome.IsError]
  | @primCodeError _ _ e _ _ he ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    cases e <;> simp_all [evalFuel, Outcome.IsError]
  | primCodeArr _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, hn]⟩
  | primCodeText _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, hn]⟩
  | primCodeClosure _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, hn]⟩
  | @primArgError _ _ _ _ e _ _ he ihc ihx =>
    obtain ⟨n1, h1⟩ := ihc
    obtain ⟨n2, h2⟩ := ihx
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    refine ⟨n1 + n2 + 1, ?_⟩
    cases e <;> simp_all [evalFuel, Outcome.IsError]
  | primArgClosure _ _ ihc ihx =>
    obtain ⟨n1, h1⟩ := ihc
    obtain ⟨n2, h2⟩ := ihx
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | primData _ _ ihc ihx =>
    obtain ⟨n1, h1⟩ := ihc
    obtain ⟨n2, h2⟩ := ihx
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | @primNameArgError _ _ _ _ e _ _ he ihc ihx =>
    obtain ⟨n1, h1⟩ := ihc
    obtain ⟨n2, h2⟩ := ihx
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    refine ⟨n1 + n2 + 1, ?_⟩
    cases e <;> simp_all [evalFuel, Outcome.IsError]
  | primNameArgClosure _ _ ihc ihx =>
    obtain ⟨n1, h1⟩ := ihc
    obtain ⟨n2, h2⟩ := ihx
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩
  | primNameData _ _ ihc ihx =>
    obtain ⟨n1, h1⟩ := ihc
    obtain ⟨n2, h2⟩ := ihx
    have h1' := evalFuel_mono h1 (m := n1 + n2) (by omega)
    have h2' := evalFuel_mono h2 (m := n1 + n2) (by omega)
    exact ⟨n1 + n2 + 1, by simp [evalFuel, h1', h2']⟩

theorem direct_iff_evalFuel {env : Env} {t : Term} {o : Outcome} :
    Direct env t o ↔ ∃ n, evalFuel n env t = some o :=
  ⟨evalFuel_complete, fun ⟨_, h⟩ => evalFuel_sound h⟩
end Reflect
