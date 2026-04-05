import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_mul_eq_smul : ↑r * a = r • a := QuaternionAlgebra.coe_mul_eq_smul r a

