import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem self_zpow₀ (a : G₀) (n : ℤ) : Commute a (a ^ n) := Commute.zpow_right₀ (Commute.refl a) n

