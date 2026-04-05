import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α]

theorem tsub_tsub_tsub_le_tsub : c - a - (c - b) ≤ b - a := by
  grw [tsub_le_iff_left, tsub_le_iff_left, add_left_comm, ← le_add_tsub, ← le_tsub_add]

