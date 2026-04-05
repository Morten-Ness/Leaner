import Mathlib

variable {α : Type u}

variable [Monoid α]

theorem divp_left_inj (u : αˣ) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b := Units.mul_left_inj _

