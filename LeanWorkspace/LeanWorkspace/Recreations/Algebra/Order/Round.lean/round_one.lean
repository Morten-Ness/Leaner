import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_one : round (1 : α) = 1 := by simp [round]

