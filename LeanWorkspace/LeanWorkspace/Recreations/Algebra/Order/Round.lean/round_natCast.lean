import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_natCast (n : ℕ) : round (n : α) = n := by simp [round]

