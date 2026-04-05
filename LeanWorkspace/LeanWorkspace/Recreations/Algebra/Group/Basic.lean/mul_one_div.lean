import Mathlib

variable {α β G M : Type*}

variable [DivInvMonoid G]

theorem mul_one_div (x y : G) : x * (1 / y) = x / y := by
  rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]

