import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_fin_one_of (a : R) : Matrix.det !![a] = a := Matrix.det_fin_one _

