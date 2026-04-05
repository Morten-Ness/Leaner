import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem mod_one (a : R) : a % 1 = 0 := EuclideanDomain.mod_eq_zero.2 (one_dvd _)

