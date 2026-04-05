import Mathlib

variable {R : Type u} [EuclideanDomain R]

variable [DecidableEq R]

theorem xgcdAux_rec {r s t r' s' t' : R} (h : r ≠ 0) :
    EuclideanDomain.xgcdAux r s t r' s' t' = EuclideanDomain.xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  conv =>
    lhs
    rw [EuclideanDomain.xgcdAux]
  exact if_neg h

