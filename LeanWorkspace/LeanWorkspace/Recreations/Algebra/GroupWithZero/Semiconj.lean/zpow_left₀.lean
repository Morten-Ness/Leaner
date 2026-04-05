import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_left₀ (h : Commute a b) (m : ℤ) : Commute (a ^ m) b := (Commute.zpow_right₀ h.symm m).symm

