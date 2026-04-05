import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

theorem gcd_dvd_right (a b : R) : gcd a b ∣ b := (EuclideanDomain.gcd_dvd a b).right

