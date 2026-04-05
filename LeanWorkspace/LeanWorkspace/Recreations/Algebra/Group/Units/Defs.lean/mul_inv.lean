import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (a b : αˣ) {u : αˣ}

theorem mul_inv : (a * ↑a⁻¹ : α) = 1 := val_inv _

