import Mathlib

variable {G : Type*}

variable [DivisionMonoid G] {a b : G}

theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a := by
  rw [← inv_eq_of_mul_eq_one_right h, inv_inv]

