import Mathlib

variable {R A : Type*}

variable [NonAssocSemiring R] [StarRing R]

theorem ofNat (n : ℕ) [n.AtLeastTwo] : IsSelfAdjoint (ofNat(n) : R) := .natCast n

