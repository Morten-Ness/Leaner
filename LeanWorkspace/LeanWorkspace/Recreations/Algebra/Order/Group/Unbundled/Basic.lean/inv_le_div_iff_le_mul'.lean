import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LE α] [MulLeftMono α] {a b c d : α}

theorem inv_le_div_iff_le_mul' : a⁻¹ ≤ b / c ↔ c ≤ a * b := by rw [inv_le_div_iff_le_mul, mul_comm]

