import Mathlib

variable {M G : Type*}

variable [Group G] [IsMulTorsionFree G] {n : ℤ} {a b : G}

theorem IsMulTorsionFree.zpow_eq_one_iff_right (ha : a ≠ 1) : a ^ n = 1 ↔ n = 0 := by simp [*]

