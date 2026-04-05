import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem div_zero (a : R) : a / 0 = 0 := EuclideanDomain.quotient_zero a

