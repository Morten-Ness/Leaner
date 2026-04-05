import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (a b : αˣ) {u : αˣ}

theorem inv_mul : (↑a⁻¹ * a : α) = 1 := inv_val _

