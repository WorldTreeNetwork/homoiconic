import Reflect

open Reflect

-- Acceptance check for `add-code-as-data`. It fails to compile until the four
-- theorems exist with exactly these signatures. No side condition on `p`.
example : ∀ p o,
    Direct [] p o ↔
    Direct [] (.app interp (.lit (reify p))) (.value (.data (reifyOutcome o))) :=
  Reflect.reflective

example : ∀ p w,
    Direct [] (.app interp (.lit (reify p))) w →
    ∃ o, w = .value (.data (reifyOutcome o)) :=
  Reflect.reflective_coverage

example : ∀ env p o,
    Direct env p o ↔
    Direct [] (.app (.app evalTerm (.lit (reify p))) (.lit (.arr (reifyEnv env))))
      (.value (.data (reifyOutcome o))) :=
  Reflect.reflective_env

example : ∀ k p o, Direct [] p o ↔ Direct [] (level k p) (lift k o) :=
  Reflect.tower

example : ∀ {env t o o'}, Direct env t o → Direct env t o' → o = o' :=
  Reflect.direct_deterministic

example : ∀ {env t o}, Direct env t o ↔ ∃ n, evalFuel n env t = some o :=
  Reflect.direct_iff_evalFuel

#print axioms Reflect.reflective
#print axioms Reflect.reflective_coverage
#print axioms Reflect.reflective_env
#print axioms Reflect.tower
#print axioms Reflect.direct_deterministic
#print axioms Reflect.direct_iff_evalFuel
