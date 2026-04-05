import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_sub_intCast (a : R) (z : ℤ) : ⌊a - z⌋ = ⌊a⌋ - z := Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (Int.floor_add_intCast _ _)

