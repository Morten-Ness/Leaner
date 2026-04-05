import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem re_intCast (z : ℤ) : (z : ℍ[R]).re = z := rfl

