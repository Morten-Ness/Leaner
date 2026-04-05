import Mathlib

variable {R K : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

theorem abs_floor_sub_le {a : R} (ha : 0 ≤ a) : |⌊a⌋₊ - a| ≤ 1 := abs_sub_comm a ⌊a⌋₊ ▸ Nat.abs_sub_floor_le ha

