import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] {a b c : α}

theorem Left.inv_le_one_iff : a⁻¹ ≤ 1 ↔ 1 ≤ a := by
  rw [← mul_le_mul_iff_left a]
  simp

