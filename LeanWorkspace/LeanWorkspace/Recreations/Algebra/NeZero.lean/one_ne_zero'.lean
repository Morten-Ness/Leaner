import Mathlib

variable {R : Type*} [Zero R]

variable {α : Type*} [Zero α]

theorem one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) ≠ 0 := one_ne_zero

