import Mathlib

variable {F α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem abs_sub_round (x : α) : |x - round x| ≤ 1 / 2 := by
  rw [round_eq, abs_sub_le_iff]
  have := floor_le (x + 1 / 2)
  have := lt_floor_add_one (x + 1 / 2)
  constructor <;> linarith

