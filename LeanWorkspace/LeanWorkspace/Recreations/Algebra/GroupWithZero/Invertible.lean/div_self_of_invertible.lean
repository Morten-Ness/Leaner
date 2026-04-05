import Mathlib

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem div_self_of_invertible (a : α) [Invertible a] : a / a = 1 := div_self (Invertible.ne_zero a)

