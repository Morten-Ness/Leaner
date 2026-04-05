import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_fin_two_of (a b c d : R) : Matrix.trace !![a, b; c, d] = a + d := Matrix.trace_fin_two _

