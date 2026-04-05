import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LE α] [MulLeftMono α] {a b c d : α}

theorem div_le_comm : a / b ≤ c ↔ a / c ≤ b := div_le_iff_le_mul'.trans div_le_iff_le_mul.symm

