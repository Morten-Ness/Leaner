import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

variable [Ring α]

theorem sub_divp (a b : α) (u : αˣ) : a - b /ₚ u = (a * u - b) /ₚ u := by
  simp only [divp, sub_mul, Units.mul_inv_cancel_right]

