import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_natCast (n : ℕ) : ↑(n : R) = (n : ℍ[R]) := rfl

