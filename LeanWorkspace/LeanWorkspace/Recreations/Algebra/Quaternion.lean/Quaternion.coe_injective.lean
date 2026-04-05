import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_injective : Function.Injective (coe : R → ℍ[R]) := QuaternionAlgebra.coe_injective

