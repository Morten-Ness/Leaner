import Mathlib

variable {G : Type*} [Group G]

theorem zpow_abs_eq_one (a : G) (n : ℤ) : a ^ |n| = 1 ↔ a ^ n = 1 := by
  rw [← Int.natCast_natAbs, zpow_natCast, pow_natAbs_eq_one]

