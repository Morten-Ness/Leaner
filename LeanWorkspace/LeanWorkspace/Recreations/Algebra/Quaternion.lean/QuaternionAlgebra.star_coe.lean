import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem star_coe : star (x : ℍ[R,c₁,c₂,c₃]) = x := by ext <;> simp

