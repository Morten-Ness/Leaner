import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem lt_floor_iff : z < ⌊a⌋ ↔ z + 1 ≤ a := by rw [← add_one_le_iff, le_floor]; norm_cast

