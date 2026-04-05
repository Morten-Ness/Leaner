import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

variable {a : R}

theorem natCast_ceil_eq_intCast_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : R) = ⌈a⌉ := by
  rw [← Int.natCast_ceil_eq_ceil ha, Int.cast_natCast]

