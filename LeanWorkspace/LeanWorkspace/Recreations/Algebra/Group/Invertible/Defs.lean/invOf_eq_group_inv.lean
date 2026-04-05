import Mathlib

variable {α : Type u}

theorem invOf_eq_group_inv [Group α] (a : α) [Invertible a] : ⅟a = a⁻¹ := invOf_eq_right_inv (mul_inv_cancel a)

