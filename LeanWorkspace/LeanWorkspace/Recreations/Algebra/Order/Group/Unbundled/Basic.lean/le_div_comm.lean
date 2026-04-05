import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LE α] [MulLeftMono α] {a b c d : α}

theorem le_div_comm : a ≤ b / c ↔ c ≤ b / a := le_div_iff_mul_le'.trans le_div_iff_mul_le.symm

