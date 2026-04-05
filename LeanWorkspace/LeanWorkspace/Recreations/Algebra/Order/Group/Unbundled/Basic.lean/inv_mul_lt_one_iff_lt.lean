import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulRightStrictMono α] {a b c : α}

theorem inv_mul_lt_one_iff_lt : a * b⁻¹ < 1 ↔ a < b := by
  rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right, one_mul]

