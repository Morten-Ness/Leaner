import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_inj {x y : R} : (x : ℍ[R]) = y ↔ x = y := Quaternion.coe_injective.eq_iff

