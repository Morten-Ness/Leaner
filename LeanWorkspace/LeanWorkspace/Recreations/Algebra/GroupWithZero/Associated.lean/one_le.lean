import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem one_le {a : Associates M} : 1 ≤ a := Dvd.intro _ (one_mul a)

