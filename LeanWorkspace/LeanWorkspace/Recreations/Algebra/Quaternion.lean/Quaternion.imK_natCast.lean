import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem imK_natCast (n : ℕ) : (n : ℍ[R]).imK = 0 := rfl

