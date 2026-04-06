import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem mod_one (a : R) : a % 1 = 0 := by
  simpa using EuclideanDomain.mod_one a
