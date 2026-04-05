import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem den_ne_zero (A : Matrix m n ℚ) : A.den ≠ 0 := by
  simp [Matrix.den, Finset.lcm_eq_zero_iff]

