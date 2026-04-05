import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_fin_two_of (a b c d : R) : Matrix.det !![a, b; c, d] = a * d - b * c := Matrix.det_fin_two _

