import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_self_zpow (a : G) (n : ℤ) : a * a ^ n = a ^ (n + 1) := by
  rw [Int.add_comm, zpow_add, zpow_one]

