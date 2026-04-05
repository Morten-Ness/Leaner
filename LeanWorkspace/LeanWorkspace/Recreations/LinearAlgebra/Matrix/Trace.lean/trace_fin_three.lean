import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_fin_three (A : Matrix (Fin 3) (Fin 3) R) : Matrix.trace A = A 0 0 + A 1 1 + A 2 2 := by
  rw [← add_zero (A 2 2), add_assoc]
  rfl

