import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

variable [Semiring α]

theorem divp_add_divp_same (a b : α) (u : αˣ) : a /ₚ u + b /ₚ u = (a + b) /ₚ u := by
  simp only [divp, add_mul]

