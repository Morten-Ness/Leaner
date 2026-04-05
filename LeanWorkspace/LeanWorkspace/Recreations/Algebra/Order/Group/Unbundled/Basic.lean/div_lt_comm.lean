import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

theorem div_lt_comm : a / b < c ↔ a / c < b := div_lt_iff_lt_mul'.trans div_lt_iff_lt_mul.symm

