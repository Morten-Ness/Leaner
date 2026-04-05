import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_add : ((x + y : R) : ℍ[R]) = x + y := QuaternionAlgebra.coe_add x y

