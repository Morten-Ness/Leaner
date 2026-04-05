import Mathlib

variable {R : Type*}

variable {p q : R}

theorem mul [NonUnitalSemiring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : Commute p q) : IsStarProjection (p * q) where
  isSelfAdjoint := (IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq
  isIdempotentElem := hp.isIdempotentElem.mul_of_commute hpq hq.isIdempotentElem

