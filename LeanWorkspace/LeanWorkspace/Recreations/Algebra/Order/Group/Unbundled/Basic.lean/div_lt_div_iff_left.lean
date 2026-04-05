import Mathlib

variable {α : Type u}

variable [Group α] [LT α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]
  {a b c : α}

theorem div_lt_div_iff_left (a : α) : a / b < a / c ↔ c < b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_lt_mul_iff_left a⁻¹, inv_mul_cancel_left,
    inv_mul_cancel_left, inv_lt_inv_iff]

