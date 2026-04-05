import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

variable [NoZeroDivisors R] [CharZero R]

theorem star_eq_neg {c₁ : R} {a : ℍ[R,c₁,0,c₃]} : star a = -a ↔ a.re = 0 := by
  simp [QuaternionAlgebra.ext_iff, eq_neg_iff_add_eq_zero]

