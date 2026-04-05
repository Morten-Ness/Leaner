import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem comm (r : R) (x : ℍ[R,c₁,c₂,c₃]) : r * x = x * r := by
  ext <;> simp [mul_comm]

