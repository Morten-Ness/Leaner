import Mathlib

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem div_mul_cancel_of_invertible (a b : α) [Invertible b] : a / b * b = a := div_mul_cancel₀ a (Invertible.ne_zero b)

