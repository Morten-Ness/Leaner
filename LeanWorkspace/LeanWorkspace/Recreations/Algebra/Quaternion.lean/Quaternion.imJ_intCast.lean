import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem imJ_intCast (z : ℤ) : (z : ℍ[R]).imJ = 0 := rfl

