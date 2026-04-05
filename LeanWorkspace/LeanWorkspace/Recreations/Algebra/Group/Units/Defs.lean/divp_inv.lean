import Mathlib

variable {α : Type u}

variable [Monoid α] {a : α}

theorem divp_inv (u : αˣ) : a /ₚ u⁻¹ = a * u := rfl

