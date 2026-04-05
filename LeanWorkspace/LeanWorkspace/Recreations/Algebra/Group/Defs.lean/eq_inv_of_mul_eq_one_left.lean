import Mathlib

variable {G : Type*}

variable [DivisionMonoid G] {a b : G}

theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ := (inv_eq_of_mul_eq_one_left h).symm

