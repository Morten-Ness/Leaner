import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem num_zero : (0 : Matrix m n ℚ).num = 0 := Matrix.num_map_natCast 0

