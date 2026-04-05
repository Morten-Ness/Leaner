import Mathlib

variable {R : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a b n : ℤ} {x : R}

theorem cast_le_neg_one_of_neg (h : a < 0) : (a : R) ≤ -1 := by
  rw [← Int.cast_one, ← Int.cast_neg, cast_le]
  exact Int.le_sub_one_of_lt h

