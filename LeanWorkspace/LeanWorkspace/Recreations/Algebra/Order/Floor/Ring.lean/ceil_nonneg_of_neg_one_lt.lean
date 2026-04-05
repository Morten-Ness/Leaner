import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem ceil_nonneg_of_neg_one_lt (ha : -1 < a) : 0 ≤ ⌈a⌉ := by
  rwa [Int.le_ceil_iff, Int.cast_zero, zero_sub]

