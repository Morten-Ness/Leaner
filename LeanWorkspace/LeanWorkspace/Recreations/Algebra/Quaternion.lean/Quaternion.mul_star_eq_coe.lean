import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem mul_star_eq_coe : a * star a = (a * star a).re := QuaternionAlgebra.mul_star_eq_coe a

