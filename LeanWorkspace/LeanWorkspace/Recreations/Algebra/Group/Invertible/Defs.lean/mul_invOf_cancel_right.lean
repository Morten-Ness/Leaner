import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem mul_invOf_cancel_right [Invertible b] : a * b * ⅟b = a := mul_invOf_cancel_right' _ _

