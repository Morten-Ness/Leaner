import Mathlib

variable {α : Type u}

theorem invOf_one' [Monoid α] {_ : Invertible (1 : α)} : ⅟(1 : α) = 1 := invOf_eq_right_inv (mul_one _)

