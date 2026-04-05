import Mathlib

open scoped Ring

variable {R : Type u}

variable [CommSemiring R] [StarRing R]

theorem starRingEnd_self_apply (x : R) : starRingEnd R (starRingEnd R x) = x := star_star x

