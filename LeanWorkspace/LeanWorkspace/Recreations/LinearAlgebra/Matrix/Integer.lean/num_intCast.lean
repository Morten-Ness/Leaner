import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem num_intCast [DecidableEq m] (a : ℤ) : (a : Matrix m m ℚ).num = a := by
  simpa [← diagonal_intCast] using Matrix.num_map_intCast (a : Matrix m m ℤ)

