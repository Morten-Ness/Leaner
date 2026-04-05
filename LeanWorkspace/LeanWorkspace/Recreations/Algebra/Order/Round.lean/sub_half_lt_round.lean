import Mathlib

variable {F α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem sub_half_lt_round (x : α) : x - 1 / 2 < round x := by
  rw [round_eq x, show x - 1 / 2 = x + 1 / 2 - 1 by linarith]
  exact Int.sub_one_lt_floor (x + 1 / 2)

