import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LE α] [MulLeftMono α] {a b c d : α}

theorem div_le_div_iff' : a / b ≤ c / d ↔ a * d ≤ c * b := by
  simpa only [div_eq_mul_inv] using mul_inv_le_mul_inv_iff'

