import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem num_neg (A : Matrix m n ℚ) : (-A).num = -A.num := by
  ext
  simp [Matrix.num]

