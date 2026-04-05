import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_fin_one_of (a : R) : Matrix.trace !![a] = a := Matrix.trace_fin_one _

