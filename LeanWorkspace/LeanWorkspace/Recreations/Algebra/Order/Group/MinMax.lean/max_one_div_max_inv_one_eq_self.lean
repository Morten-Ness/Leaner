import Mathlib

variable {α : Type*} [Group α] [LinearOrder α] [MulLeftMono α]

theorem max_one_div_max_inv_one_eq_self (a : α) : max a 1 / max a⁻¹ 1 = a := by
  rcases le_total a 1 with (h | h) <;> simp [h]

alias max_zero_sub_eq_self := max_zero_sub_max_neg_zero_eq_self

