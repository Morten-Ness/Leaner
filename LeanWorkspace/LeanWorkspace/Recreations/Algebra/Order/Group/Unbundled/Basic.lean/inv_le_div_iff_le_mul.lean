import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LE α] [MulLeftMono α] {a b c d : α}

theorem inv_le_div_iff_le_mul : b⁻¹ ≤ a / c ↔ c ≤ a * b := le_div_iff_mul_le.trans inv_mul_le_iff_le_mul'

