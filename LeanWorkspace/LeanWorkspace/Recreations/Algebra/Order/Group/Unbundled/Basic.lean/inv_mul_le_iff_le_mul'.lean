import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LE α] [MulLeftMono α] {a b c d : α}

theorem inv_mul_le_iff_le_mul' : c⁻¹ * a ≤ b ↔ a ≤ b * c := by rw [inv_mul_le_iff_le_mul, mul_comm]

