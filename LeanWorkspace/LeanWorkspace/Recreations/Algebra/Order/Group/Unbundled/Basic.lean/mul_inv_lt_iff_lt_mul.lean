import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulRightStrictMono α] {a b c : α}

theorem mul_inv_lt_iff_lt_mul : a * b⁻¹ < c ↔ a < c * b := by
  rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right]

