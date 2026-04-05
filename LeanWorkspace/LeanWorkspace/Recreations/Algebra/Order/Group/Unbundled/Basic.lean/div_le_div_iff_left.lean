import Mathlib

variable {α : Type u}

variable [Group α] [LE α]

variable [MulLeftMono α] [MulRightMono α] {a b c : α}

theorem div_le_div_iff_left (a : α) : a / b ≤ a / c ↔ c ≤ b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_le_mul_iff_left a⁻¹, inv_mul_cancel_left,
    inv_mul_cancel_left, inv_le_inv_iff]

