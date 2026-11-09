import Circular

open Circular

-- This acceptance check deliberately fails until both general theorems exist.
-- The signatures retain all quote-free terms, all outcomes, and coverage.
example : ∀ p (h : Circular.Pure p), ∀ o,
    Direct [] p o ↔
    ∃ w, Direct [] (.app interpreterBody (encode p h)) w ∧ Represents o w :=
  Circular.metacircular

example : ∀ p (h : Circular.Pure p), ∀ w,
    Direct [] (.app interpreterBody (encode p h)) w →
    ∃ o, Represents o w :=
  Circular.coverage

#print axioms Circular.metacircular
#print axioms Circular.coverage
