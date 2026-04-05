import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem star_coe : star (x : ℍ[R]) = x := QuaternionAlgebra.star_coe x

