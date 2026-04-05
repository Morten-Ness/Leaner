import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [Group α] {a b : α}

variable [MulLeftMono α]

theorem leOnePart_eq_one : a⁻ᵐ = 1 ↔ 1 ≤ a := by simp [leOnePart_eq_one']

