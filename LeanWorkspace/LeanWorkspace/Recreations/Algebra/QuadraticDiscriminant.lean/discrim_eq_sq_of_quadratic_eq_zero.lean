import Mathlib

variable {R : Type*}

variable [CommRing R] {a b c : R}

theorem discrim_eq_sq_of_quadratic_eq_zero {x : R} (h : a * (x * x) + b * x + c = 0) :
    discrim a b c = (2 * a * x + b) ^ 2 := by
  rw [discrim]
  linear_combination -4 * a * h

