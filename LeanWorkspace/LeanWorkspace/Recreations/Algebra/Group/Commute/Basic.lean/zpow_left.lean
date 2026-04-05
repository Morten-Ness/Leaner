import Mathlib

variable {G : Type*}

variable [Group G] {a b : G}

theorem zpow_left (h : Commute a b) (m : ℤ) : Commute (a ^ m) b := (Commute.zpow_right h.symm m).symm

