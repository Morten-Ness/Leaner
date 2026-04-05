import Mathlib

variable {M : Type*} {S T : Set M}

variable [MulOneClass M]

theorem one_mem_center : (1 : M) ∈ Set.center M where
  comm _ := by rw [commute_iff_eq, one_mul, mul_one]
  left_assoc _ _ := by rw [one_mul, one_mul]
  right_assoc _ _ := by rw [mul_one, mul_one]

