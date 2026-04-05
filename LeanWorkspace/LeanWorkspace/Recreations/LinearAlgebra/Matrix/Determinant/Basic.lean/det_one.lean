import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_one : Matrix.det (1 : Matrix n n R) = 1 := by rw [← diagonal_one]; simp [-diagonal_one]

