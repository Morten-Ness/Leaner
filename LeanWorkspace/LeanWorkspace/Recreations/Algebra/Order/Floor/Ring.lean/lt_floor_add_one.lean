import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem lt_floor_add_one (a : R) : a < ⌊a⌋ + 1 := by
  simpa only [Int.succ, Int.cast_add, Int.cast_one] using Int.lt_succ_floor a

