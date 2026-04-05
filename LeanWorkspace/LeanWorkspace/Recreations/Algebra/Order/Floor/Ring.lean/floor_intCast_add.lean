import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_intCast_add (z : ℤ) (a : R) : ⌊↑z + a⌋ = z + ⌊a⌋ := by
  simpa only [add_comm] using Int.floor_add_intCast a z

