import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulRightMono α] {a b c : α}

theorem le_mul_inv_iff_le : 1 ≤ a * b⁻¹ ↔ b ≤ a := by
  rw [← mul_le_mul_iff_right b, one_mul, inv_mul_cancel_right]

