import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem one_le_ceil_iff : 1 ≤ ⌈a⌉ ↔ 0 < a := by
  simpa using Int.le_ceil_iff (z := 1)

