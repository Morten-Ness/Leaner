import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem floor_le_sub_one_iff : ⌊a⌋ ≤ z - 1 ↔ a < z := by rw [← floor_lt, le_sub_one_iff]

