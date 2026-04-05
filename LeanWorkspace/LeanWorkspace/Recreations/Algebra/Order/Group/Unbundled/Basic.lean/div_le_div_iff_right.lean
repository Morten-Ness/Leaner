import Mathlib

variable {α : Type u}

variable [Group α] [LE α]

variable [MulRightMono α] {a b c : α}

theorem div_le_div_iff_right (c : α) : a / c ≤ b / c ↔ a ≤ b := by
  simpa only [div_eq_mul_inv] using mul_le_mul_iff_right _

