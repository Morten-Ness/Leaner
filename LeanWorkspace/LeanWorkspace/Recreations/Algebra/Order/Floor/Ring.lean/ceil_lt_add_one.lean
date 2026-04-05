import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_lt_add_one (a : R) : (⌈a⌉ : R) < a + 1 := by
  rw [← lt_ceil, ← Int.cast_one, Int.ceil_add_intCast]
  apply lt_add_one

