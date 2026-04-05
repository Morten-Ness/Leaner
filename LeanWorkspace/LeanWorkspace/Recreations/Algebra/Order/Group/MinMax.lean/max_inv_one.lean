import Mathlib

variable {α : Type*} [Group α] [LinearOrder α] [MulLeftMono α]

theorem max_inv_one (a : α) : max a⁻¹ 1 = a⁻¹ * max a 1 := by
  rw [eq_inv_mul_iff_mul_eq, ← eq_div_iff_mul_eq', max_one_div_max_inv_one_eq_self]

