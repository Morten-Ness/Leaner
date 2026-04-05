import Mathlib

variable {R A : Type*}

variable [NonAssocSemiring R] [StarRing R]

theorem natCast (n : ℕ) : IsSelfAdjoint (n : R) := star_natCast _

