import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_neg : ((-x : R) : ℍ[R]) = -x := QuaternionAlgebra.coe_neg x

