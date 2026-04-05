import Mathlib

variable {K : Type*} [Field K]

theorem gcd_eq_of_ne [DecidableEq K] {a : K} (ha : a ≠ 0) (b : K) :
    EuclideanDomain.gcd a b = a := by
  rw [Field.gcd_eq, if_neg ha]

