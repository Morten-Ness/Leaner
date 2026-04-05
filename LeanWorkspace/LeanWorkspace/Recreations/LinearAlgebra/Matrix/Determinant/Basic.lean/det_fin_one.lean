import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_fin_one (A : Matrix (Fin 1) (Fin 1) R) : Matrix.det A = A 0 0 := Matrix.det_unique A

