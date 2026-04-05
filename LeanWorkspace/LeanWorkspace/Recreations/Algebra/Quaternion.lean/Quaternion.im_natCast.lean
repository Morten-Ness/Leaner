import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem im_natCast (n : ℕ) : (n : ℍ[R]).im = 0 := rfl

