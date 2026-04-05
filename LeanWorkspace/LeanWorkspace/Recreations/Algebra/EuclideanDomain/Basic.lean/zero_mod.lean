import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem zero_mod (b : R) : 0 % b = 0 := EuclideanDomain.mod_eq_zero.2 (dvd_zero _)

