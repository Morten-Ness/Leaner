import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_le_iff_tsub_le : a - b ≤ c ↔ a - c ≤ b := by rw [tsub_le_iff_left, tsub_le_iff_right]

