import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [AddGroup R]

theorem coe_neg : ((-x : R) : ℍ[R,c₁,c₂,c₃]) = -x := by ext <;> simp

