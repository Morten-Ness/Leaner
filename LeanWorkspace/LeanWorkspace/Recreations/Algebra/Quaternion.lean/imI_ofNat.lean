import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [AddCommGroupWithOne R]

theorem imI_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

