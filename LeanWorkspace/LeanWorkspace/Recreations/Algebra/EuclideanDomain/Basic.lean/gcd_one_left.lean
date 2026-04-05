import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

theorem gcd_one_left (a : R) : gcd 1 a = 1 := EuclideanDomain.gcd_eq_left.2 (one_dvd _)

