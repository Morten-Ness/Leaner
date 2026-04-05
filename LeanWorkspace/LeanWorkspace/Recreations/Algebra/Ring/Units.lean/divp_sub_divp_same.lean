import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

variable [Ring α]

theorem divp_sub_divp_same (a b : α) (u : αˣ) : a /ₚ u - b /ₚ u = (a - b) /ₚ u := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Units.neg_divp, Units.divp_add_divp_same]

