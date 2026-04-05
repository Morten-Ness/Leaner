import Mathlib

variable {R : Type u} [EuclideanDomain R]

variable [DecidableEq R]

theorem xgcd_zero_left {s t r' s' t' : R} : EuclideanDomain.xgcdAux 0 s t r' s' t' = (r', s', t') := by
  unfold EuclideanDomain.xgcdAux
  exact if_pos rfl

