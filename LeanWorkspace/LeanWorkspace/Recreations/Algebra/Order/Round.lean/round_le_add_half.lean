import Mathlib

variable {F α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_le_add_half (x : α) : round x ≤ x + 1 / 2 := by
  rw [round_eq x]
  exact Int.floor_le (x + 1 / 2)

