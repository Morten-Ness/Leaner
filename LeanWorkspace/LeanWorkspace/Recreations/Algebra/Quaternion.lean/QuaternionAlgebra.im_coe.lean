import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [AddGroup R]

theorem im_coe : (x : ℍ[R,c₁,c₂,c₃]).im = 0 := rfl

