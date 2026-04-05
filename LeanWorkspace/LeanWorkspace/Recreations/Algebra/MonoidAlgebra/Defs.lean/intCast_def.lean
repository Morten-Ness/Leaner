import Mathlib

variable {R S G M N O ι : Type*}

variable [Ring R]

theorem intCast_def [MulOneClass M] (z : ℤ) : (z : R[M]) = single 1 (z : R) := rfl

