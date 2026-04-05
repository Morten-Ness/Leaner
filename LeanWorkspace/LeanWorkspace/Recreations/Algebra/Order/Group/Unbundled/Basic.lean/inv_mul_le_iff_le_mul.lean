import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] {a b c : α}

theorem inv_mul_le_iff_le_mul : b⁻¹ * a ≤ c ↔ a ≤ b * c := by
  rw [← mul_le_mul_iff_left b, mul_inv_cancel_left]

