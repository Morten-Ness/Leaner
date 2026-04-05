import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_add_intCast (x : α) (y : ℤ) : round (x + y) = round x + y := by
  rw [round, round, Int.fract_add_intCast, Int.floor_add_intCast, Int.ceil_add_intCast,
    ← apply_ite₂, ite_self]

