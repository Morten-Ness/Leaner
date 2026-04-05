import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_right₀ (h : Commute a b) : ∀ m : ℤ, Commute a (b ^ m) := SemiconjBy.zpow_right₀ h

