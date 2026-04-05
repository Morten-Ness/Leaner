import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem associated_map_mk {f : Associates M →* M} (hinv : Function.RightInverse f Associates.mk)
    (a : M) : a ~ᵤ f (Associates.mk a) := Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm

