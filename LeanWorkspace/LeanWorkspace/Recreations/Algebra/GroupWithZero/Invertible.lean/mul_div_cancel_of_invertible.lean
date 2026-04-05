import Mathlib

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem mul_div_cancel_of_invertible (a b : α) [Invertible b] : a * b / b = a := mul_div_cancel_right₀ a (Invertible.ne_zero b)

