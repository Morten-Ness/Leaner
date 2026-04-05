import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_mul_cancel_right [Invertible b] : a * ⅟b * b = a := invOf_mul_cancel_right' _ _

