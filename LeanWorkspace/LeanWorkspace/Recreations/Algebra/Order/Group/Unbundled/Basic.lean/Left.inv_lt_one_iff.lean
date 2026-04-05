import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulLeftStrictMono α] {a b c : α}

theorem Left.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a := by
  rw [← mul_lt_mul_iff_left a, mul_inv_cancel, mul_one]

