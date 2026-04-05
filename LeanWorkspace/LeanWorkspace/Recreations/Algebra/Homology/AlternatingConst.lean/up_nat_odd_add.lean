import Mathlib

theorem up_nat_odd_add {i j : ℕ} (h : (ComplexShape.up ℕ).Rel i j) : Odd (i + j) := by
  subst h
  norm_num

