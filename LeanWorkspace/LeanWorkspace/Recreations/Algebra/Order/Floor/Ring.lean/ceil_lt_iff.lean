import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem ceil_lt_iff : ⌈a⌉ < z ↔ a ≤ z - 1 := by rw [← le_sub_one_iff, ceil_le]; norm_cast

