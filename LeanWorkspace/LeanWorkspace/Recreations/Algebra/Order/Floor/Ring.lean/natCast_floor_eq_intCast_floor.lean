import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

variable {a : R}

theorem natCast_floor_eq_intCast_floor (ha : 0 ≤ a) : (⌊a⌋₊ : R) = ⌊a⌋ := by
  rw [← Int.natCast_floor_eq_floor ha, Int.cast_natCast]

