import Mathlib

variable {G : Type*}

variable [Group G] {a b : G}

theorem zpow_right (h : Commute a b) (m : ℤ) : Commute a (b ^ m) := SemiconjBy.zpow_right h m

