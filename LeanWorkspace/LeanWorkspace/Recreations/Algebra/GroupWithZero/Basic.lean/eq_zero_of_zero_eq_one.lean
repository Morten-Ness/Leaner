import Mathlib

variable {M₀ G₀ : Type*}

variable [MulZeroOneClass M₀]

theorem eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0 := by
  rw [← mul_one a, ← h, mul_zero]

