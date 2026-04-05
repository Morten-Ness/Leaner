import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_intCast_add (x : α) (y : ℤ) : round ((y : α) + x) = y + round x := by
  rw [add_comm, round_add_intCast, add_comm]

