import Mathlib

variable {α : Type u}

variable [Group α] [LT α]

variable [MulRightStrictMono α] {a b c : α}

theorem div_lt_div_iff_right (c : α) : a / c < b / c ↔ a < b := by
  simpa only [div_eq_mul_inv] using mul_lt_mul_iff_right _

