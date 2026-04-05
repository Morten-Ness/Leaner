import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem mul_invOf_cancel_left [Invertible a] : a * (⅟a * b) = b := mul_invOf_cancel_left' a b

