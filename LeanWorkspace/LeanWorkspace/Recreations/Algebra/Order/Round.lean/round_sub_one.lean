import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_sub_one (a : α) : round (a - 1) = round a - 1 := by
  rw [← round_sub_intCast a 1, cast_one]

