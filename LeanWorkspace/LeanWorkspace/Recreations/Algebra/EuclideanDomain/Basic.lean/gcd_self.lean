import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

theorem gcd_self (a : R) : gcd a a = a := EuclideanDomain.gcd_eq_left.2 dvd_rfl

