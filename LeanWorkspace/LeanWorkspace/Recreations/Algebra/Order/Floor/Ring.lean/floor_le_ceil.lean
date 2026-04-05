import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_le_ceil (a : R) : ⌊a⌋ ≤ ⌈a⌉ := cast_le.1 <| (floor_le _).trans <| le_ceil _

