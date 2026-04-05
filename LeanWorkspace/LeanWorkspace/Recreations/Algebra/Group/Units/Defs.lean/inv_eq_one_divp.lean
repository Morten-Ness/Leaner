import Mathlib

variable {α : Type u}

variable [Monoid α] {a : α}

theorem inv_eq_one_divp (u : αˣ) : ↑u⁻¹ = 1 /ₚ u := by rw [one_divp]

