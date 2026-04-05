import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_intCast (n : ℤ) : round (n : α) = n := by simp [round]

