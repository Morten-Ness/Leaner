import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_lt_ceil_of_lt {a b : R} (h : a < b) : ⌊a⌋ < ⌈b⌉ := cast_lt.1 <| (floor_le a).trans_lt <| h.trans_le <| le_ceil b

