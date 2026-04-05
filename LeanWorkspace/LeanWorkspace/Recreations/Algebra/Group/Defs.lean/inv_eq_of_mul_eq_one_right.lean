import Mathlib

variable {G : Type*}

variable [DivisionMonoid G] {a b : G}

theorem inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b := DivisionMonoid.inv_eq_of_mul _ _

