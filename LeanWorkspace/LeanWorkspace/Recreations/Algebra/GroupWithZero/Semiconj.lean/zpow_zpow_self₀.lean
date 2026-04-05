import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_zpow_self₀ (a : G₀) (m n : ℤ) : Commute (a ^ m) (a ^ n) := Commute.zpow_zpow₀ (Commute.refl a) m n

