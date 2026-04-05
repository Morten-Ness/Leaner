import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem coe_pow (n : ℕ) : (↑(x ^ n) : ℍ[R,c₁,c₂,c₃]) = (x : ℍ[R,c₁,c₂,c₃]) ^ n := (algebraMap R ℍ[R,c₁,c₂,c₃]).map_pow x n

