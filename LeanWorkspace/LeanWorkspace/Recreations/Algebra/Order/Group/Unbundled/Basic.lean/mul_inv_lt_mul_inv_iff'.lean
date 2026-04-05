import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

theorem mul_inv_lt_mul_inv_iff' : a * b⁻¹ < c * d⁻¹ ↔ a * d < c * b := by
  rw [mul_comm c, mul_inv_lt_inv_mul_iff, mul_comm]

