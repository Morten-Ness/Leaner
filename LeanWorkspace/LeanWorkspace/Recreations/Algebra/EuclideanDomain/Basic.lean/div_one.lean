import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem div_one (p : R) : p / 1 = p := (EuclideanDomain.eq_div_of_mul_eq_left (one_ne_zero' R) (mul_one p)).symm

