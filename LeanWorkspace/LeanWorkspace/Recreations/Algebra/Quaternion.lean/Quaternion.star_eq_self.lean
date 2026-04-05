import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

variable [NoZeroDivisors R] [CharZero R]

theorem star_eq_self {a : ℍ[R]} : star a = a ↔ a = a.re := QuaternionAlgebra.star_eq_self

