import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_eq_zero_of_isEmpty [IsEmpty n] (A : Matrix n n R) : Matrix.trace A = 0 := by simp [Matrix.trace]

