import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [Zero R]

theorem imI_coe : (x : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

