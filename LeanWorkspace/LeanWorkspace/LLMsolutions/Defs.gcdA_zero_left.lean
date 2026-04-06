import Mathlib

variable {R : Type u} [EuclideanDomain R]

variable [DecidableEq R]

theorem gcdA_zero_left {s : R} : EuclideanDomain.gcdA 0 s = 0 := by
  simpa using EuclideanDomain.gcdA_zero_left s
