import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem den_one [DecidableEq m] : (1 : Matrix m m ℚ).den = 1 := Matrix.den_natCast 1

