import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

variable {a : R}

theorem natCast_ceil_eq_intCast_ceil_of_neg_one_lt (ha : -1 < a) : (⌈a⌉₊ : R) = ⌈a⌉ := by
  rw [← Int.natCast_ceil_eq_ceil_of_neg_one_lt ha, Int.cast_natCast]

