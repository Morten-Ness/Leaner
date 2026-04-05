import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] [IsStrictOrderedRing R] {a : R}

theorem ceil_lt_add_one_of_gt_neg_one (ha : -1 < a) : ⌈a⌉₊ < a + 1 := by
  by_cases! h : 0 ≤ a
  · exact Int.ceil_lt_add_one h
  · rw [ceil_eq_zero.mpr h.le, cast_zero]
    exact neg_lt_iff_pos_add.mp ha

