import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_zero : Matrix.trace (0 : Matrix n n R) = 0 := (Finset.sum_const (0 : R)).trans <| smul_zero _

