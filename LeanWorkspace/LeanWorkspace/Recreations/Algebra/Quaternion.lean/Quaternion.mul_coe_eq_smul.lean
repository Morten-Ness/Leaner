import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem mul_coe_eq_smul : a * r = r • a := QuaternionAlgebra.mul_coe_eq_smul r a

