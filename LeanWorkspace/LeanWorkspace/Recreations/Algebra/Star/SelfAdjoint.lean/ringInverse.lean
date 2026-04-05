import Mathlib

variable {R A : Type*}

variable [NonAssocSemiring R] [StarRing R]

theorem ringInverse {a : A} [Semiring A] [StarRing A]
    (ha : IsSelfAdjoint a) : IsSelfAdjoint a⁻¹ʳ := by
  rw [isSelfAdjoint_iff, ← Ring.inverse_star, IsSelfAdjoint.star_eq ha]

