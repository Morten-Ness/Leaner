import Mathlib

variable {α : Type u}

variable [Monoid α] {a : α}

theorem one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹ := one_mul _

