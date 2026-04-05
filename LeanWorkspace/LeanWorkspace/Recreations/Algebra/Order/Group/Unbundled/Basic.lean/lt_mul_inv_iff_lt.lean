import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulRightStrictMono α] {a b c : α}

theorem lt_mul_inv_iff_lt : 1 < a * b⁻¹ ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mul, inv_mul_cancel_right]

