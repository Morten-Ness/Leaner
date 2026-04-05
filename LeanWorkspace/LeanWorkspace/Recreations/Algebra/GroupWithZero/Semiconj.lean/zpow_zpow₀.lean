import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_zpow₀ (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) := Commute.zpow_right₀ (Commute.zpow_left₀ h m) n

