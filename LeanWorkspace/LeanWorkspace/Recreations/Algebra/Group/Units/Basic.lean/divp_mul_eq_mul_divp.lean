import Mathlib

variable {α : Type u}

variable [CommMonoid α]

theorem divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u * y = x * y /ₚ u := by
  rw [divp, divp, mul_right_comm]

