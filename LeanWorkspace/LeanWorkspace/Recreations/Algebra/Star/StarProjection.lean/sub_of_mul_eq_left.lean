import Mathlib

variable {R : Type*}

variable {p q : R}

theorem sub_of_mul_eq_left [NonUnitalNonAssocRing R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = p) :
    IsStarProjection (q - p) where
  isSelfAdjoint := hq.isSelfAdjoint.sub hp.isSelfAdjoint
  isIdempotentElem := hp.isIdempotentElem.sub
    hq.isIdempotentElem hpq
    (by simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hpq)))

