import Mathlib

variable {R : Type*}

variable {p q : R}

theorem add [NonUnitalNonAssocSemiring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) :
    IsStarProjection (p + q) where
  isSelfAdjoint := hp.isSelfAdjoint.add hq.isSelfAdjoint
  isIdempotentElem := hp.isIdempotentElem.add hq.isIdempotentElem <| by
    rw [hpq, zero_add]
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hpq))

