import Mathlib

variable {R : Type u} [EuclideanDomain R]

variable [DecidableEq R]

theorem gcdB_zero_left {s : R} : EuclideanDomain.gcdB 0 s = 1 := by
  unfold EuclideanDomain.gcdB
  rw [EuclideanDomain.xgcd, EuclideanDomain.xgcd_zero_left]

