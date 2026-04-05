import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem sub_self_nonneg : 0 ≤ a - a := by
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
  · rw [sub_self_eq_zero_of_ne_top ha]

