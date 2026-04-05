import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem den_zero : (0 : Matrix m n ℚ).den = 1 := Matrix.den_map_natCast 0

