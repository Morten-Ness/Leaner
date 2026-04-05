import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

variable [Semiring α]

theorem divp_add (a b : α) (u : αˣ) : a /ₚ u + b = (a + b * u) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]

