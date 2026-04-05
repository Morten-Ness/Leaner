import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

theorem mul_inv_lt_iff_le_mul' : a * b⁻¹ < c ↔ a < b * c := by
  rw [← inv_mul_lt_iff_lt_mul, mul_comm]

