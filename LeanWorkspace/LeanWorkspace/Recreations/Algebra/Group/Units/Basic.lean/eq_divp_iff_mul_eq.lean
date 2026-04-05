import Mathlib

variable {α : Type u}

variable [Monoid α]

theorem eq_divp_iff_mul_eq {x : α} {u : αˣ} {y : α} : x = y /ₚ u ↔ x * u = y := by
  rw [eq_comm, divp_eq_iff_mul_eq]

