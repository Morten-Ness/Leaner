import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_self₀ (a : G₀) (n : ℤ) : Commute (a ^ n) a := Commute.zpow_left₀ (Commute.refl a) n

