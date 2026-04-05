import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem imK_intCast (z : ℤ) : (z : ℍ[R]).imK = 0 := rfl

