import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_sub_one (a : R) : ⌈a - 1⌉ = ⌈a⌉ - 1 := by
  rw [eq_sub_iff_add_eq, ← Int.ceil_add_one, sub_add_cancel]

