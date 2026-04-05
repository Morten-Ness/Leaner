import Mathlib

variable {α : Type u}

variable [Monoid α] {a : α}

theorem mul_divp_cancel (a : α) (u : αˣ) : a * u /ₚ u = a := (mul_assoc _ _ _).trans <| by rw [Units.mul_inv, mul_one]

