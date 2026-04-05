import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

theorem inv_lt_div_iff_lt_mul' : b⁻¹ < a / c ↔ c < a * b := lt_div_iff_mul_lt.trans inv_mul_lt_iff_lt_mul'

