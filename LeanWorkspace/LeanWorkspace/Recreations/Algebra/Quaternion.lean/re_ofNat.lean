import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [AddCommGroupWithOne R]

theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).re = ofNat(n) := rfl

