import Mathlib

variable {R K : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

theorem sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋₊ := sub_lt_iff_lt_add.2 <| Nat.lt_floor_add_one a

