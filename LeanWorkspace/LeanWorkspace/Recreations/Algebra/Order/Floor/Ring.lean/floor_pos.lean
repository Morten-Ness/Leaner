import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem floor_pos : 0 < ⌊a⌋ ↔ 1 ≤ a := by
  rw [Int.lt_iff_add_one_le, zero_add, le_floor, cast_one]

