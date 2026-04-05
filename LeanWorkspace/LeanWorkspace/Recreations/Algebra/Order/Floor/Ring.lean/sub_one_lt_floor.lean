import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋ := sub_lt_iff_lt_add.2 (Int.lt_floor_add_one a)

