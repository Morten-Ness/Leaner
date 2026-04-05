import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] {a b c : α}

theorem Left.one_le_inv_iff : 1 ≤ a⁻¹ ↔ a ≤ 1 := by
  rw [← mul_le_mul_iff_left a]
  simp

