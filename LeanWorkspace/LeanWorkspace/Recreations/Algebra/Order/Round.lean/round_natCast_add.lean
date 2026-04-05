import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_natCast_add (x : α) (y : ℕ) : round ((y : α) + x) = y + round x := by
  rw [add_comm, round_add_natCast, add_comm]

