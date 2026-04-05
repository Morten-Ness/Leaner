import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LE α] [MulLeftMono α] {a b c d : α}

theorem mul_inv_le_mul_inv_iff' : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b := by
  rw [mul_comm c, mul_inv_le_inv_mul_iff, mul_comm]

