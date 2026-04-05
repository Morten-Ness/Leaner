import Mathlib

open scoped Ring

variable {R : Type u}

variable [CommSemiring R] [StarRing R]

theorem RingHom.star_def {S : Type*} [NonAssocSemiring S] (f : S →+* R) :
    Star.star f = RingHom.comp (starRingEnd R) f := rfl

