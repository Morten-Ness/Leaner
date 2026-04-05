import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_sub_intCast (x : α) (y : ℤ) : round (x - y) = round x - y := by
  rw [sub_eq_add_neg]
  norm_cast
  rw [round_add_intCast, sub_eq_add_neg]

