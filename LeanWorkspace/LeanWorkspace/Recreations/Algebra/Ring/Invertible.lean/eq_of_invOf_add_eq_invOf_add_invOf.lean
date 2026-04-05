import Mathlib

open scoped Ring

variable {R : Type*}

theorem eq_of_invOf_add_eq_invOf_add_invOf [Ring R] {a b : R} [Invertible a] [Invertible b]
    [Invertible (a + b)] (h : ⅟(a + b) = ⅟a + ⅟b) :
    a * ⅟b * a = b * ⅟a * b := by
  have h' := neg_one_eq_invOf_mul_add_invOf_mul_iff.mp h
  have h_a_binv_a : -(b + a) = a * ⅟b * a := neg_add_eq_mul_invOf_mul_same_iff.mpr h'
  have h_b_ainv_b : -(a + b) = b * ⅟a * b := by
    rw [add_comm] at h'
    exact neg_add_eq_mul_invOf_mul_same_iff.mpr h'
  rw [← h_a_binv_a, ← h_b_ainv_b, add_comm]

