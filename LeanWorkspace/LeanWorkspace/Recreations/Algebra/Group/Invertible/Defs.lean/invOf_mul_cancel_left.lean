import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_mul_cancel_left [Invertible a] : ⅟a * (a * b) = b := invOf_mul_cancel_left' _ _

