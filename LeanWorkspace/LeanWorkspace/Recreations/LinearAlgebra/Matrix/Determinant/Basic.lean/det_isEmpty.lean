import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_isEmpty [IsEmpty n] {A : Matrix n n R} : Matrix.det A = 1 := by simp [Matrix.det_apply]

