import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_intCast (z : ℤ) : ↑(z : R) = (z : ℍ[R]) := rfl

