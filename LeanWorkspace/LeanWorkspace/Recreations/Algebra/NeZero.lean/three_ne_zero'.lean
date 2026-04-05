import Mathlib

variable {R : Type*} [Zero R]

variable {α : Type*} [Zero α]

theorem three_ne_zero' [OfNat α 3] [NeZero (3 : α)] : (3 : α) ≠ 0 := three_ne_zero

