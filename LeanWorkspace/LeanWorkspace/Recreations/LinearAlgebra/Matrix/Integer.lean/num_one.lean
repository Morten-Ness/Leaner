import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem num_one [DecidableEq m] : (1 : Matrix m m ℚ).num = 1 := Matrix.num_natCast 1

