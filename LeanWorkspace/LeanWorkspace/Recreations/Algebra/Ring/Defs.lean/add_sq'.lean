import Mathlib

variable {α : Type u} {R : Type v}

variable [CommSemiring α]

theorem add_sq' (a b : α) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [add_sq, add_assoc, add_comm _ (b ^ 2), add_assoc]

alias add_pow_two := add_sq

