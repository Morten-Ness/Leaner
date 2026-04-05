import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_isEmpty [IsEmpty n] {A : Matrix n n R} : Matrix.permanent A = 1 := by simp [Matrix.permanent]

