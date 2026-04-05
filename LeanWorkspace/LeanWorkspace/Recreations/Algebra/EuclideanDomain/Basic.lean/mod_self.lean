import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem mod_self (a : R) : a % a = 0 := EuclideanDomain.mod_eq_zero.2 dvd_rfl

