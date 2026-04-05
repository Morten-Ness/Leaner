import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommMonoid α] [Sub α] [OrderedSub α] {a b : α}

theorem tsub_nonpos : a - b ≤ 0 ↔ a ≤ b := by rw [tsub_le_iff_left, add_zero]

alias ⟨_, tsub_nonpos_of_le⟩ := tsub_nonpos

