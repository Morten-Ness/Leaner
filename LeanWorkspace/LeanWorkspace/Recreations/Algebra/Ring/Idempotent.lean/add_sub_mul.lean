import Mathlib

variable {R : Type*}

variable [CommRing R] {a b : R}

theorem add_sub_mul (hp : IsIdempotentElem a) (hq : IsIdempotentElem b) :
    IsIdempotentElem (a + b - a * b) := IsIdempotentElem.add_sub_mul_of_commute (.all ..) hp hq

