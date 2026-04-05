import Mathlib

variable {R : Type*} [Zero R]

variable {α : Type*} [Zero α]

theorem two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) ≠ 0 := NeZero.ne (2 : α)

