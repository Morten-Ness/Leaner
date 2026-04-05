import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_add_one (a : R) : ⌊a + 1⌋ = ⌊a⌋ + 1 := by
  rw [← cast_one, Int.floor_add_intCast]

