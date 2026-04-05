import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem num_eq_zero_iff (A : Matrix m n ℚ) : A.num = 0 ↔ A = 0 := by
  simp [Matrix.num, ← ext_iff, A.den_ne_zero]

