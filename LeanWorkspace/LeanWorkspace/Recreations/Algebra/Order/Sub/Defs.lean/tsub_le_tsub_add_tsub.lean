import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α]

theorem tsub_le_tsub_add_tsub : a - c ≤ a - b + (b - c) := by
  grw [tsub_le_iff_left, ← add_assoc, add_right_comm, ← le_add_tsub, ← le_add_tsub]

