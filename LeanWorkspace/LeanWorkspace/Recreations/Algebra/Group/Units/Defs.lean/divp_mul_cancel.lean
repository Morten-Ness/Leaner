import Mathlib

variable {α : Type u}

variable [Monoid α] {a : α}

theorem divp_mul_cancel (a : α) (u : αˣ) : a /ₚ u * u = a := (mul_assoc _ _ _).trans <| by rw [Units.inv_mul, mul_one]

