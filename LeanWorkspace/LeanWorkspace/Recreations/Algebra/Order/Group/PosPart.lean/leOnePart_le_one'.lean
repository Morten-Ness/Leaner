import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [Group α] {a b : α}

theorem leOnePart_le_one' : a⁻ᵐ ≤ 1 ↔ a⁻¹ ≤ 1 := by simp [leOnePart]

