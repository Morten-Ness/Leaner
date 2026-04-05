import Mathlib

variable {α β G M : Type*}

variable [DivInvOneMonoid G]

theorem div_one (a : G) : a / 1 = a := by simp [div_eq_mul_inv]

