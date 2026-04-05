import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

theorem gcd_dvd_left (a b : R) : gcd a b ∣ a := (EuclideanDomain.gcd_dvd a b).left

