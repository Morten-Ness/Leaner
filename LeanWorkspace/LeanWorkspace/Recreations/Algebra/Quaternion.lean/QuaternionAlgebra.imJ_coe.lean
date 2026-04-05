import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [Zero R]

theorem imJ_coe : (x : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

