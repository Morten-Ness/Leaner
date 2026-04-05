import Mathlib

variable {K : Type*} [Field K] [NeZero (2 : K)] {a b c : K}

theorem quadratic_eq_zero_iff_of_discrim_eq_zero (ha : a ≠ 0) (h : discrim a b c = 0) (x : K) :
    a * (x * x) + b * x + c = 0 ↔ x = -b / (2 * a) := by
  have : discrim a b c = 0 * 0 := by rw [h, mul_zero]
  rw [quadratic_eq_zero_iff ha this, add_zero, sub_zero, or_self_iff]

