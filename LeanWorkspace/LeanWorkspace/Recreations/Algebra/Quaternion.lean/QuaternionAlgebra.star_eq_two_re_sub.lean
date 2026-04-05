import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem star_eq_two_re_sub : star a = ↑(2 * a.re + c₂ * a.imI) - a := eq_sub_iff_add_eq.2 QuaternionAlgebra.star_add_self' a

