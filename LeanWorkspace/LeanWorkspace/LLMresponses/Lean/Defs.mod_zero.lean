import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem mod_zero (a : R) : a % 0 = a := by
  simpa using EuclideanDomain.mod_zero a
