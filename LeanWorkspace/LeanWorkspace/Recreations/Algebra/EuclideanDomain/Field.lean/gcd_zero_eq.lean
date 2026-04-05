import Mathlib

variable {K : Type*} [Field K]

theorem gcd_zero_eq [DecidableEq K] (b : K) :
    EuclideanDomain.gcd 0 b = b := by
  rw [Field.gcd_eq, if_pos rfl]

