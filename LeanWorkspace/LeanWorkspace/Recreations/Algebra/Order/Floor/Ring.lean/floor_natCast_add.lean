import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_natCast_add (n : ℕ) (a : R) : ⌊↑n + a⌋ = n + ⌊a⌋ := by
  rw [← Int.cast_natCast, Int.floor_intCast_add]

