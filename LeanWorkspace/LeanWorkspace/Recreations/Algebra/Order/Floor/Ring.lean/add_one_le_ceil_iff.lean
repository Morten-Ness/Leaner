import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem add_one_le_ceil_iff : z + 1 ≤ ⌈a⌉ ↔ (z : R) < a := by rw [← lt_ceil, add_one_le_iff]

