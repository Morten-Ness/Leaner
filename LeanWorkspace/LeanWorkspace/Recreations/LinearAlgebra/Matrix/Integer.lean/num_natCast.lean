import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem num_natCast [DecidableEq m] (a : ℕ) : (a : Matrix m m ℚ).num = a := by
  simpa [← diagonal_natCast] using Matrix.num_map_natCast (a : Matrix m m ℕ)

