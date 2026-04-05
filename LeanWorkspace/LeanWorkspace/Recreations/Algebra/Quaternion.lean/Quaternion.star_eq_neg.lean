import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

variable [NoZeroDivisors R] [CharZero R]

theorem star_eq_neg {a : ℍ[R]} : star a = -a ↔ a.re = 0 := QuaternionAlgebra.star_eq_neg

