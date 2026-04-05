import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_neg : ⌊-a⌋ = -⌈a⌉ := eq_of_forall_le_iff fun z => by rw [le_neg, ceil_le, le_floor, Int.cast_neg, le_neg]

