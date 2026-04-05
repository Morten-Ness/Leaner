import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem le_ceil_iff : z ≤ ⌈a⌉ ↔ z - 1 < a := by rw [← sub_one_lt_iff, lt_ceil]; norm_cast

