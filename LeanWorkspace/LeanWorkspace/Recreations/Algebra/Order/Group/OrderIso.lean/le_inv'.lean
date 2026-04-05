import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] [MulRightMono α] {a b : α}

theorem le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := (OrderIso.inv α).le_symm_apply

