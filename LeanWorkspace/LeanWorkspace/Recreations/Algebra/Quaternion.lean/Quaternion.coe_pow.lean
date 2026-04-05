import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_pow (n : ℕ) : (↑(x ^ n) : ℍ[R]) = (x : ℍ[R]) ^ n := QuaternionAlgebra.coe_pow x n

