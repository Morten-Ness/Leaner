import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_fin_three_of (a b c d e f g h i : R) :
    Matrix.trace !![a, b, c; d, e, f; g, h, i] = a + e + i := Matrix.trace_fin_three _

