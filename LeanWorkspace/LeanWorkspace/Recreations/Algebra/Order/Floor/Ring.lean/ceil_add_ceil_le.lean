import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_add_ceil_le (a b : R) : ⌈a⌉ + ⌈b⌉ ≤ ⌈a + b⌉ + 1 := by
  rw [← le_sub_iff_add_le, ceil_le, Int.cast_sub, Int.cast_add, Int.cast_one, le_sub_comm]
  refine (Int.ceil_lt_add_one _).le.trans ?_
  rw [le_sub_iff_add_le', ← add_assoc, add_le_add_iff_right]
  exact le_ceil _

