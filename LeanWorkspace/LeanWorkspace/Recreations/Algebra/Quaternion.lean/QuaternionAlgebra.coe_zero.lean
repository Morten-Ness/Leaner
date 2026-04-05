import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [Zero R]

theorem coe_zero : ((0 : R) : ℍ[R,c₁,c₂,c₃]) = 0 := rfl

