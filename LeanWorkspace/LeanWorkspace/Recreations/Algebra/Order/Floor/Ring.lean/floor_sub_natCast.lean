import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_sub_natCast (a : R) (n : ℕ) : ⌊a - n⌋ = ⌊a⌋ - n := by
  rw [← Int.cast_natCast, Int.floor_sub_intCast]

