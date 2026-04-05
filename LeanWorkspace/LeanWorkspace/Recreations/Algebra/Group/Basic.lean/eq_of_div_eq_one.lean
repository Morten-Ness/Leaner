import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem eq_of_div_eq_one (h : a / b = 1) : a = b := inv_injective <| inv_eq_of_mul_eq_one_right <| by rwa [← div_eq_mul_inv]

