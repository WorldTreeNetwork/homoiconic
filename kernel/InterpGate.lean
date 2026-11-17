import Reflect.Correctness

open Reflect

example : ∀ [Ops], ∀ p o,
    Direct [] p o ↔
    Direct [] (.app interp (.lit (reify p))) (.value (.data (reifyOutcome o))) :=
  Reflect.reflective

example : ∀ [Ops], ∀ p w,
    Direct [] (.app interp (.lit (reify p))) w →
    ∃ o, w = .value (.data (reifyOutcome o)) :=
  Reflect.reflective_coverage

example : ∀ [Ops], ∀ env p o,
    Direct env p o ↔
    Direct [] (.app (.app evalTerm (.lit (reify p))) (.lit (.arr (reifyEnv env))))
      (.value (.data (reifyOutcome o))) :=
  Reflect.reflective_env

example : ∀ [Ops], ∀ k p o, Direct [] p o ↔ Direct [] (level k p) (lift k o) :=
  Reflect.tower

#print axioms Reflect.reflective
#print axioms Reflect.reflective_coverage
#print axioms Reflect.reflective_env
#print axioms Reflect.tower
