import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_commutes : ↑r * a = a * r := QuaternionAlgebra.coe_commutes r a

