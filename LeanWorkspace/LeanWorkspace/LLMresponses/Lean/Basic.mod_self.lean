import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem mod_self (a : R) : a % a = 0 := by
  simpa using EuclideanDomain.mod_self a
