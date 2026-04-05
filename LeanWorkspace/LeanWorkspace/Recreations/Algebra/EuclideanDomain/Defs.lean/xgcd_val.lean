import Mathlib

variable {R : Type u} [EuclideanDomain R]

variable [DecidableEq R]

theorem xgcd_val (x y : R) : EuclideanDomain.xgcd x y = (EuclideanDomain.gcdA x y, EuclideanDomain.gcdB x y) := rfl

