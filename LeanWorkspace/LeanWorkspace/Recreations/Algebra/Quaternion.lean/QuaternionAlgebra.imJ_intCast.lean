import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [AddCommGroupWithOne R]

theorem imJ_intCast (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

