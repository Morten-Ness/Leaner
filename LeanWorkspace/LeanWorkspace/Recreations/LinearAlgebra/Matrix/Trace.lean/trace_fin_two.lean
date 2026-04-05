import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : Matrix.trace A = A 0 0 + A 1 1 := congr_arg (_ + ·) (add_zero (A 1 1))

