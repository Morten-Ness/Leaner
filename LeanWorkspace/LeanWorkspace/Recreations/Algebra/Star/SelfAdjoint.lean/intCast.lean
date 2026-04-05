import Mathlib

variable {R A : Type*}

variable [Ring R] [StarRing R]

theorem intCast (z : ℤ) : IsSelfAdjoint (z : R) := star_intCast _

