import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_zpow_self (a : G) (n : ℤ) : a ^ n * a = a ^ (n + 1) := (zpow_add_one ..).symm

