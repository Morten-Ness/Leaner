import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem star_mul_eq_coe : star a * a = (star a * a).re := QuaternionAlgebra.star_mul_eq_coe a

