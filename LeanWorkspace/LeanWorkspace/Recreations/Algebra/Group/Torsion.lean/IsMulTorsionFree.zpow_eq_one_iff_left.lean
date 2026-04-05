import Mathlib

variable {M G : Type*}

variable [Group G] [IsMulTorsionFree G] {n : ℤ} {a b : G}

theorem IsMulTorsionFree.zpow_eq_one_iff_left (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  rw [← zpow_left_inj (a := a) hn, one_zpow]

-- We want to use `IsAddTorsion.zsmul_eq_zero_iff` earlier than `smul_eq_zero`.

