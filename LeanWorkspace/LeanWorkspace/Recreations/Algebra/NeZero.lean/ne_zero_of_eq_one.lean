import Mathlib

variable {R : Type*} [Zero R]

variable {α : Type*} [Zero α]

theorem ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h : a = 1) : a ≠ 0 := h ▸ one_ne_zero

