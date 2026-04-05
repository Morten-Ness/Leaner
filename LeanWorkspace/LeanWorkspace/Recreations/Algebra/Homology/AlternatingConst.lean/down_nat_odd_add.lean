import Mathlib

theorem down_nat_odd_add {i j : ℕ} (h : (ComplexShape.down ℕ).Rel i j) : Odd (i + j) := by
  subst h
  norm_num

