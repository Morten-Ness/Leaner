import Mathlib

variable {α β G M : Type*}

variable [DivInvMonoid G]

theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by simp only [mul_assoc, div_eq_mul_inv]

