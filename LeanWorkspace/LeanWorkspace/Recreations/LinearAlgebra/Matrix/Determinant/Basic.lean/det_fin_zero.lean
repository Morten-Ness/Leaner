import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_fin_zero {A : Matrix (Fin 0) (Fin 0) R} : Matrix.det A = 1 := Matrix.det_isEmpty

