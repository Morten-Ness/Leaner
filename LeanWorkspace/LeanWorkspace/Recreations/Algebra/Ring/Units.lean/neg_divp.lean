import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

variable [Monoid α] [HasDistribNeg α]

theorem neg_divp (a : α) (u : αˣ) : -(a /ₚ u) = -a /ₚ u := by simp only [divp, neg_mul]

