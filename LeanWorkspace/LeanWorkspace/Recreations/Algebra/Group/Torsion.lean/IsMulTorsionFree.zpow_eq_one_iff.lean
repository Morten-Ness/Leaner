import Mathlib

variable {M G : Type*}

variable [Group G] [IsMulTorsionFree G] {n : ℤ} {a b : G}

theorem IsMulTorsionFree.zpow_eq_one_iff : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [zpow_eq_one_iff_left, *]

