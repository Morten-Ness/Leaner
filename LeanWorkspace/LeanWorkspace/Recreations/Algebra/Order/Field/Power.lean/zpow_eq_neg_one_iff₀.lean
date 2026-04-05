import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

theorem zpow_eq_neg_one_iff₀ : a ^ n = -1 ↔ a = -1 ∧ Odd n := by
  simpa using zpow_eq_neg_zpow_iff₀ (α := α) one_ne_zero

