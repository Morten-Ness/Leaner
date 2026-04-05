import Mathlib

variable {R : Type u} [EuclideanDomain R]

variable [DecidableEq R]

theorem gcdA_zero_left {s : R} : EuclideanDomain.gcdA 0 s = 0 := by
  unfold EuclideanDomain.gcdA
  rw [EuclideanDomain.xgcd, EuclideanDomain.xgcd_zero_left]

