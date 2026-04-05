import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulLeftStrictMono α] {a b c : α}

theorem inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c := by
  rw [← mul_lt_mul_iff_left b, mul_inv_cancel_left]

