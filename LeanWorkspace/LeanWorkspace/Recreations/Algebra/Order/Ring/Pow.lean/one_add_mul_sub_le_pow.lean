import Mathlib

variable {R : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R} {n : ℕ}

theorem one_add_mul_sub_le_pow (H : -1 ≤ a) (n : ℕ) : 1 + n * (a - 1) ≤ a ^ n := by
  have : -2 ≤ a - 1 := by
    rwa [← one_add_one_eq_two, neg_add, ← sub_eq_add_neg, sub_le_sub_iff_right]
  simpa only [add_sub_cancel] using one_add_mul_le_pow this n

