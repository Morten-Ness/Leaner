import Mathlib

variable {α : Type u}

variable [Group α] [LT α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]
  {a b c : α}

theorem inv_lt_div_iff_lt_mul : a⁻¹ < b / c ↔ c < a * b := by
  rw [div_eq_mul_inv, lt_mul_inv_iff_mul_lt, inv_mul_lt_iff_lt_mul]

