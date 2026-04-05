import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem divp_eq_div [DivisionMonoid α] (a : α) (u : αˣ) : a /ₚ u = a / u := by
  rw [div_eq_mul_inv, divp, u.val_inv_eq_inv_val]

