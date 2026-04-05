import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem star_mul_eq_coe : star a * a = (star a * a).re := by ext <;> simp <;> ring

