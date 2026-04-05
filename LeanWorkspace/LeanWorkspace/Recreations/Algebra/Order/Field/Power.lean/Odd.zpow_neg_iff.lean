import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

theorem Odd.zpow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 := by
  refine ⟨lt_imp_lt_of_le_imp_le (zpow_nonneg · _), fun ha ↦ ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add_one₀ ha.ne]
  exact mul_neg_of_pos_of_neg (Even.zpow_pos (even_two_mul _) ha.ne) ha

protected lemma Odd.zpow_nonneg_iff (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 hn.zpow_neg_iff

