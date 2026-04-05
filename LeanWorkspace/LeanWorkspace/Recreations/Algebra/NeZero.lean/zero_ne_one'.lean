import Mathlib

variable {R : Type*} [Zero R]

variable {α : Type*} [Zero α]

theorem zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) ≠ 1 := zero_ne_one

