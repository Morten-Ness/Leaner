import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

theorem mul_inv_cancel_right (a : α) (b : αˣ) : a * b * ↑b⁻¹ = a := by
  rw [mul_assoc, mul_inv, mul_one]

