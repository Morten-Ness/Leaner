import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem floor_le_iff : ⌊a⌋ ≤ z ↔ a < z + 1 := by rw [← lt_add_one_iff, floor_lt]; norm_cast

