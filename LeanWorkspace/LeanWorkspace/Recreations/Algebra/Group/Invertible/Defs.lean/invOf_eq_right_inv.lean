import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_eq_right_inv [Invertible a] (hac : a * b = 1) : ⅟a = b := left_inv_eq_right_inv (invOf_mul_self _) hac

