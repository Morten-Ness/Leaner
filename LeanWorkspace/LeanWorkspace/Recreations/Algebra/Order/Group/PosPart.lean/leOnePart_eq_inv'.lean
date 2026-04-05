import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [Group α] {a b : α}

theorem leOnePart_eq_inv' : a⁻ᵐ = a⁻¹ ↔ 1 ≤ a⁻¹ := sup_eq_left

