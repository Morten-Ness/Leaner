import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] [MulRightMono α] {a b : α}

theorem inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := (OrderIso.inv α).symm_apply_le

alias ⟨inv_le_of_inv_le', _⟩ := inv_le'

attribute [to_additive neg_le_of_neg_le] inv_le_of_inv_le'

