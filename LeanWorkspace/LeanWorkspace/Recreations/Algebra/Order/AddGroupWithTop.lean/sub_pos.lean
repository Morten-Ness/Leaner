import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem sub_pos : 0 < a - b ↔ b < a ∨ b = ⊤ := by
  obtain rfl | hb := eq_or_ne b ⊤
  · simp
  · simp [← sub_self_eq_zero_of_ne_top hb, hb]

