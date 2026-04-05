import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

theorem xgcdAux_val (x y : R) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by
  rw [xgcd, ← EuclideanDomain.xgcdAux_fst x y 1 0 0 1]

