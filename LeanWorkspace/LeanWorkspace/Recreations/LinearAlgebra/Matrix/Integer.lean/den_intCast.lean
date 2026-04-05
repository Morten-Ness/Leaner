import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem den_intCast [DecidableEq m] (a : ℤ) : (a : Matrix m m ℚ).den = 1 := by
  simpa [← diagonal_intCast] using Matrix.den_map_intCast (a : Matrix m m ℤ)

