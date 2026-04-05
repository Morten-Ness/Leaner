import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem re_natCast (n : ℕ) : (n : ℍ[R]).re = n := rfl

