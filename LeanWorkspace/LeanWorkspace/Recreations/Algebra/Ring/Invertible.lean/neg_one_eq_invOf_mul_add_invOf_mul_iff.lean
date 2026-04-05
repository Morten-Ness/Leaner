import Mathlib

open scoped Ring

variable {R : Type*}

theorem neg_one_eq_invOf_mul_add_invOf_mul_iff [Ring R] {a b : R} [Invertible a]
    [Invertible b] [Invertible (a + b)] : ⅟(a + b) = ⅟a + ⅟b ↔ -1 = ⅟a * b + ⅟b * a := by
  calc ⅟(a + b) = ⅟a + ⅟b
      ↔ ⅟(a + b) * (a + b) = (⅟a + ⅟b) * (a + b) := by rw [mul_left_inj_of_invertible]
    _ ↔ 1 = ⅟a * a + ⅟b * a + (⅟a * b + ⅟b * b) := by rw [invOf_mul_self, mul_add, add_mul, add_mul]
    _ ↔ 1 = 1 + ⅟b * a + (1 + ⅟a * b) := by rw [invOf_mul_self, invOf_mul_self, add_comm _ 1]
    _ ↔ 1 = 1 + 1 + ⅟b * a + ⅟a * b := by rw [← add_assoc, add_comm _ 1, ← add_assoc]
    _ ↔ -2 + 1 = -2 + (2 + ⅟b * a + ⅟a * b) := by rw [one_add_one_eq_two, add_right_inj]
    _ ↔ -2 + 1 = ⅟b * a + ⅟a * b := by rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add]
    _ ↔ -1 + 0 = ⅟b * a + ⅟a * b := by rw [← one_add_one_eq_two, neg_add, add_assoc, neg_add_cancel]
    _ ↔ -1 = ⅟a * b + ⅟b * a := by rw [add_zero, add_comm]

