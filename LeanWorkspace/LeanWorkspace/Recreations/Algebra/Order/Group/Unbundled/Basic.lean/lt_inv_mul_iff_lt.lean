import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulLeftStrictMono α] {a b c : α}

theorem lt_inv_mul_iff_lt : 1 < b⁻¹ * a ↔ b < a := by
  rw [← mul_lt_mul_iff_left b, mul_one, mul_inv_cancel_left]

