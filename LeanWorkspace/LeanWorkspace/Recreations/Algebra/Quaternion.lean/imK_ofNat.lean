import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [AddCommGroupWithOne R]

theorem imK_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

