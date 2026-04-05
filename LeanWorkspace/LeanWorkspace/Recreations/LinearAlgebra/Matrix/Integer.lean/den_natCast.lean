import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem den_natCast [DecidableEq m] (a : ℕ) : (a : Matrix m m ℚ).den = 1 := by
  simpa [← diagonal_natCast] using Matrix.den_map_natCast (a : Matrix m m ℕ)

