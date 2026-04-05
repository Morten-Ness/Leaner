import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

variable [MulRightStrictMono α]

theorem mul_inv_lt_inv_mul_iff : a * b⁻¹ < d⁻¹ * c ↔ d * a < c * b := by
  rw [← mul_lt_mul_iff_left d, ← mul_lt_mul_iff_right b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]

