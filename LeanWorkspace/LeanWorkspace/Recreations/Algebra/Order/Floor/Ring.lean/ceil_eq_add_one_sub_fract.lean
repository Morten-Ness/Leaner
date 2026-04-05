import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_eq_add_one_sub_fract (ha : fract a ≠ 0) : (⌈a⌉ : R) = a + 1 - fract a := by
  rw [(or_iff_right ha).mp (Int.fract_eq_zero_or_add_one_sub_ceil a)]
  abel

