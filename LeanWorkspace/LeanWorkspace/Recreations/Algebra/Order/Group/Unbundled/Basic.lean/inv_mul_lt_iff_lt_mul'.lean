import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

theorem inv_mul_lt_iff_lt_mul' : c⁻¹ * a < b ↔ a < b * c := by rw [inv_mul_lt_iff_lt_mul, mul_comm]

