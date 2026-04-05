import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_fin_zero (A : Matrix (Fin 0) (Fin 0) R) : Matrix.trace A = 0 := rfl

