import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

theorem div_lt_div_iff' : a / b < c / d ↔ a * d < c * b := by
  simpa only [div_eq_mul_inv] using mul_inv_lt_mul_inv_iff'

