import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LE α] [MulLeftMono α] {a b c d : α}

theorem mul_inv_le_iff_le_mul' : a * b⁻¹ ≤ c ↔ a ≤ b * c := by
  rw [← inv_mul_le_iff_le_mul, mul_comm]

