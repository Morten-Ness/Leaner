import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem floor_le_neg_one_iff : ⌊a⌋ ≤ -1 ↔ a < 0 := by
  simpa using Int.floor_le_iff (z := -1)

