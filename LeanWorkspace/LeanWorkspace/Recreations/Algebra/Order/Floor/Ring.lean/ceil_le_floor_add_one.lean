import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem ceil_le_floor_add_one (a : R) : ⌈a⌉ ≤ ⌊a⌋ + 1 := by
  rw [ceil_le, Int.cast_add, Int.cast_one]
  exact (Int.lt_floor_add_one a).le

