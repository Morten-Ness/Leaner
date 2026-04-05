import Mathlib

variable {R : Type*} [Zero R]

variable {α : Type*} [Zero α]

theorem four_ne_zero' [OfNat α 4] [NeZero (4 : α)] : (4 : α) ≠ 0 := four_ne_zero

