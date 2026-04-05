import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem smul_coe : x • (y : ℍ[R]) = ↑(x * y) := QuaternionAlgebra.smul_coe x y

