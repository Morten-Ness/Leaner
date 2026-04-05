import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

theorem lt_div_comm : a < b / c ↔ c < b / a := lt_div_iff_mul_lt'.trans lt_div_iff_mul_lt.symm

