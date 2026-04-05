import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_fin_one (A : Matrix (Fin 1) (Fin 1) R) : Matrix.trace A = A 0 0 := add_zero _

