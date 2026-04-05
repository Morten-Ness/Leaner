import Mathlib

variable {R : Type*}

variable {p q : R}

theorem sub_of_mul_eq_right [NonUnitalNonAssocRing R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q * p = p) :
    IsStarProjection (q - p) := IsStarProjection.sub_of_mul_eq_left hp hq
  (by simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hqp)))

