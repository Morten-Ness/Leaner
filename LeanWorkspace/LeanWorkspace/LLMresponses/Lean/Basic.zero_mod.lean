import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem zero_mod (b : R) : 0 % b = 0 := by
  simpa using mod_zero_left b
