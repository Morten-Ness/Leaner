import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

variable [NoZeroDivisors R] [CharZero R]

theorem star_eq_self {c₁ c₂ : R} {a : ℍ[R,c₁,c₂,c₃]} : star a = a ↔ a = a.re := by
  simp_all [QuaternionAlgebra.ext_iff, neg_eq_iff_add_eq_zero, add_self_eq_zero]

