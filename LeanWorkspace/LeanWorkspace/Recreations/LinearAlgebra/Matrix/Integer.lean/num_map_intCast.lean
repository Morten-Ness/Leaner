import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem num_map_intCast (A : Matrix m n ℤ) : (A.map (↑)).num = A := by
  simp [Matrix.num, Function.comp_def]

