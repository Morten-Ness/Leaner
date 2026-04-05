import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem imI_intCast (z : ℤ) : (z : ℍ[R]).imI = 0 := rfl

