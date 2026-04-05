import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem mul_right_not_lt {a : R} (b) (h : a ≠ 0) : ¬a * b ≺ b := by
  rw [mul_comm]
  exact mul_left_not_lt b h

