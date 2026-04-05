import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [AddCommGroupWithOne R]

theorem coe_intCast (z : ℤ) : ↑(z : R) = (z : ℍ[R,c₁,c₂,c₃]) := rfl

