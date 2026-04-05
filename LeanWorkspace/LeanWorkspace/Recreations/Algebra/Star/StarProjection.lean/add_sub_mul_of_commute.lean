import Mathlib

variable {R : Type*}

variable {p q : R}

theorem add_sub_mul_of_commute [NonUnitalRing R] [StarRing R]
    (hpq : Commute p q) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (p + q - p * q) where
  isIdempotentElem := hp.isIdempotentElem.add_sub_mul_of_commute hpq hq.isIdempotentElem
  isSelfAdjoint := .sub (IsStarProjection.add hp.isSelfAdjoint hq.isSelfAdjoint)
    ((IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq)

