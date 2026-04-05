import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [Group α] {a b : α}

theorem leOnePart_eq_one' : a⁻ᵐ = 1 ↔ a⁻¹ ≤ 1 := sup_eq_right

