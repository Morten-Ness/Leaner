import Mathlib

variable {α : Type u}

variable [Monoid α] {a : α}

theorem divp_assoc (a b : α) (u : αˣ) : a * b /ₚ u = a * (b /ₚ u) := mul_assoc _ _ _

