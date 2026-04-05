import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [Zero R]

variable [One R]

theorem coe_one : ((1 : R) : ℍ[R,c₁,c₂,c₃]) = 1 := rfl

