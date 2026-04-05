import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_one_add (a : G) (n : ℤ) : a ^ (1 + n) = a * a ^ n := by rw [zpow_add, zpow_one]

