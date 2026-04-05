import Mathlib

variable {F α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_eq (x : α) : round x = ⌊x + 1 / 2⌋ := by
  rw [← cast_mul_floor_div_cancel_of_pos two_pos, round_eq_div]
  simp [mul_add]

