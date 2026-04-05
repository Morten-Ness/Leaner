import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] {a b c : α}

theorem le_inv_mul_iff_mul_le : b ≤ a⁻¹ * c ↔ a * b ≤ c := by
  rw [← mul_le_mul_iff_left a]
  simp

