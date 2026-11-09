import Circular.Closing

namespace Circular

inductive IsLambda : Term → Prop where
  | lam : IsLambda (.lam b)

inductive Step : Term → Term → Prop where
  | beta (hv : IsLambda v) : Step (.app (.lam b) v) (plug [v] 0 b)
  | left : Step f f' → Step (.app f a) (.app f' a)
  | right : IsLambda f → Step a a' → Step (.app f a) (.app f a')

inductive Red : Term → Term → Prop where
  | refl : Red t t
  | cons : Step t u → Red u v → Red t v

namespace Red
 theorem single (h : Step t u) : Red t u := .cons h .refl
 theorem trans (h : Red t u) (h' : Red u v) : Red t v := by
  induction h with
  | refl => exact h'
  | cons hs _ ih => exact .cons hs (ih h')
 theorem left (h : Red t u) : Red (.app t a) (.app u a) := by
  induction h with
  | refl => exact .refl
  | cons hs _ ih => exact .cons (.left hs) ih
 theorem right (hf : IsLambda f) (h : Red t u) : Red (.app f t) (.app f u) := by
  induction h with
  | refl => exact .refl
  | cons hs _ ih => exact .cons (.right hf hs) ih
end Red

/-- Counts beta contractions, including function and argument position.
    The clock belongs to the proof; object programs have no fuel parameter. -/
inductive BetaN : Nat → Term → Term → Prop where
  | lam : BetaN 0 (.lam b) (.lam b)
  | app : BetaN nf f (.lam b) → BetaN na a v → BetaN nb (plug [v] 0 b) r →
      BetaN (nf + na + nb + 1) (.app f a) r

namespace BetaN
 theorem forget (h : BetaN n t r) : Beta t r := by
  induction h with
  | lam => exact .lam
  | app _ _ _ ihf iha ihb => exact .app ihf iha ihb
 theorem value (h : BetaN n t r) : IsLambda r := by
  obtain ⟨b, rfl⟩ := beta_value h.forget
  exact .lam
 theorem of_beta (h : Beta t r) : ∃ n, BetaN n t r := by
  induction h with
  | lam => exact ⟨0, .lam⟩
  | app _ _ _ ihf iha ihb =>
    obtain ⟨nf, hf⟩ := ihf
    obtain ⟨na, ha⟩ := iha
    obtain ⟨nb, hb⟩ := ihb
    exact ⟨_, .app hf ha hb⟩
 theorem step (hs : Step t u) (h : BetaN n t r) : ∃ m, m < n ∧ BetaN m u r := by
  induction hs generalizing n r with
  | beta hv =>
    cases h with
    | app hf ha hb =>
      cases hf
      cases hv
      cases ha
      exact ⟨_, by omega, hb⟩
  | left hs ih =>
    cases h with
    | app hf ha hb =>
      obtain ⟨m, hm, hmf⟩ := ih hf
      exact ⟨_, by omega, .app hmf ha hb⟩
  | right hv hs ih =>
    cases h with
    | app hf ha hb =>
      obtain ⟨m, hm, hma⟩ := ih ha
      exact ⟨_, by omega, .app hf hma hb⟩
 theorem red (hs : Red t u) (h : BetaN n t r) : ∃ m, m ≤ n ∧ BetaN m u r := by
  induction hs generalizing n with
  | refl => exact ⟨n, Nat.le_refl _, h⟩
  | cons hs _ ih =>
    obtain ⟨m, hm, hmu⟩ := h.step hs
    obtain ⟨k, hk, hkv⟩ := ih hmu
    exact ⟨k, by omega, hkv⟩
end BetaN

namespace Beta
 theorem step_back (hs : Step t u) (h : Beta u r) : Beta t r := by
  induction hs generalizing r with
  | beta hv => cases hv; exact .app .lam .lam h
  | left hs ih =>
    cases h with
    | app hf ha hb => exact .app (ih hf) ha hb
  | right hv hs ih =>
    cases h with
    | app hf ha hb => exact .app hf (ih ha) hb
 theorem red_back (hs : Red t u) (h : Beta u r) : Beta t r := by
  induction hs with
  | refl => exact h
  | cons hs _ ih => exact (ih h).step_back hs
 theorem of_lambda (h : IsLambda t) : Beta t t := by cases h; exact .lam
end Beta

/-- A syntactic CBV stepper used to certify finite administrative reductions. -/
def next : Term → Option Term
  | .app (.lam b) (.lam v) => some (plug [.lam v] 0 b)
  | .app (.lam b) a => (next a).map (.app (.lam b))
  | .app f a => (next f).map (fun f' => .app f' a)
  | _ => none

theorem next_sound (h : next t = some u) : Step t u := by
  induction t using next.induct generalizing u with
  | case1 b v => cases h; exact .beta .lam
  | case2 b a _ ih =>
    simp only [next, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    exact .right .lam (ih ha)
  | case3 f a _ _ ih =>
    simp only [next, Option.map_eq_some_iff] at h
    obtain ⟨f', hf, rfl⟩ := h
    exact .left (ih hf)
  | case4 => simp_all [next]

def reduce : Nat → Term → Term
  | 0, t => t
  | n + 1, t => reduce n ((next t).getD t)

theorem reduce_sound (n : Nat) (t : Term) : Red t (reduce n t) := by
  induction n generalizing t with
  | zero => exact .refl
  | succ n ih =>
    simp only [reduce]
    cases hn : next t with
    | none => simpa only [Option.getD_none] using ih t
    | some t' => exact .cons (next_sound hn) (ih t')

end Circular
