import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] {a b c : α}

theorem le_inv_mul_iff_le : 1 ≤ b⁻¹ * a ↔ b ≤ a := by
  rw [← mul_le_mul_iff_left b, mul_one, mul_inv_cancel_left]

