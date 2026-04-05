import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_zero [Nonempty n] : Matrix.permanent (0 : Matrix n n R) = 0 := by simp [Matrix.permanent]

