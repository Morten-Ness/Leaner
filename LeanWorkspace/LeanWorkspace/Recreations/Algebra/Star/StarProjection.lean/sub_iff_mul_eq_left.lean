import Mathlib

variable {R : Type*}

variable {p q : R}

theorem sub_iff_mul_eq_left [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R]
    {p q : R} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (q - p) ↔ p * q = p := by
  rw [isStarProjection_iff, hp.isIdempotentElem.sub_iff hq.isIdempotentElem]
  simp_rw [hq.isSelfAdjoint.sub hp.isSelfAdjoint, and_true]
  nth_rw 3 [← hp.isSelfAdjoint]
  nth_rw 2 [← hq.isSelfAdjoint]
  rw [← star_mul, star_eq_iff_star_eq, hp.isSelfAdjoint, eq_comm]
  simp_rw [and_self]

