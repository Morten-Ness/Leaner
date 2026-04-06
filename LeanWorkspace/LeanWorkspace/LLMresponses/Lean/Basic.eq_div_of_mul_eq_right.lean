FAIL
import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem eq_div_of_mul_eq_right {a b c : R} (ha : a ≠ 0) (h : a * b = c) : b = c / a := by
  rw [← h]
  simpa [mul_comm] using euclideanDomain_mul_div_cancel a b ha
