FAIL
import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem eq_div_of_mul_eq_left {a b c : R} (hb : b ≠ 0) (h : a * b = c) : a = c / b := by
  rw [← h]
  exact (div_eq_iff hb).2 rfl
