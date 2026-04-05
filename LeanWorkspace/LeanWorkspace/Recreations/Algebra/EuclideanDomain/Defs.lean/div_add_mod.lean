import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem div_add_mod (a b : R) : b * (a / b) + a % b = a := EuclideanDomain.quotient_mul_add_remainder_eq _ _

