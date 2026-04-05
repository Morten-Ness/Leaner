import Mathlib

variable {α β G M : Type*}

variable [DivInvMonoid G]

theorem div_eq_mul_one_div (a b : G) : a / b = a * (1 / b) := by rw [div_eq_mul_inv, one_div]

