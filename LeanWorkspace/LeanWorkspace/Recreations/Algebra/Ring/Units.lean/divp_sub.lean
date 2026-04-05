import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

variable [Ring α]

theorem divp_sub (a b : α) (u : αˣ) : a /ₚ u - b = (a - b * u) /ₚ u := by
  simp only [divp, sub_mul, sub_right_inj]
  rw [mul_assoc, Units.mul_inv, mul_one]

