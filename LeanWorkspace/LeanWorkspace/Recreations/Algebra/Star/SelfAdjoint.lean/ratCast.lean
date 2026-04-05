import Mathlib

variable {R A : Type*}

variable [DivisionRing R] [StarRing R]

theorem ratCast (x : ℚ) : IsSelfAdjoint (x : R) := star_ratCast _

