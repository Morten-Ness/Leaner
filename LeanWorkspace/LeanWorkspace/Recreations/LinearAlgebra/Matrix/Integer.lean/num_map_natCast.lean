import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem num_map_natCast (A : Matrix m n ℕ) : (A.map (↑)).num = A.map (↑) := by
  simp [Matrix.num, Function.comp_def]

