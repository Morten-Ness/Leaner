import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] {a b c d : α}

variable [MulRightMono α]

theorem mul_inv_le_inv_mul_iff : a * b⁻¹ ≤ d⁻¹ * c ↔ d * a ≤ c * b := by
  rw [← mul_le_mul_iff_left d, ← mul_le_mul_iff_right b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]

