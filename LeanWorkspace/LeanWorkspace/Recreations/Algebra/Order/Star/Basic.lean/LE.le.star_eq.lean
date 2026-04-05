import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem LE.le.star_eq {x : R} (hx : 0 ≤ x) : star x = x := hx.isSelfAdjoint.star_eq

