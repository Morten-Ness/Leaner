import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [AddZeroClass R]

theorem coe_add : ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x + y := by ext <;> simp

