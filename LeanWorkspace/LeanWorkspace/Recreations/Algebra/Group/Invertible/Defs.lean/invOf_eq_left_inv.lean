import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_eq_left_inv [Invertible a] (hac : b * a = 1) : ⅟a = b := (left_inv_eq_right_inv hac (mul_invOf_self _)).symm

