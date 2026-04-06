import Mathlib

variable {R : Type u} [EuclideanDomain R]

variable [DecidableEq R]

theorem gcdB_zero_left {s : R} : EuclideanDomain.gcdB 0 s = 1 := by
  simpa using EuclideanDomain.gcdB_zero_left (R := R) s
