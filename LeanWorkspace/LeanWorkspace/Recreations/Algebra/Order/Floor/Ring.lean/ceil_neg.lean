import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_neg : ⌈-a⌉ = -⌊a⌋ := eq_of_forall_ge_iff fun z => by rw [neg_le, ceil_le, le_floor, Int.cast_neg, neg_le]

