import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [Preorder α] [MulLeftStrictMono α] {a b c d : α}

theorem div_lt_div'' (hab : a < b) (hcd : c < d) : a / d < b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_lt_inv_mul_iff, mul_comm]
  exact mul_lt_mul_of_lt_of_lt hab hcd

