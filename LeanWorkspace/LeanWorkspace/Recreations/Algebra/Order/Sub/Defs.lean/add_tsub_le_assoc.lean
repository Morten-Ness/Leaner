import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α]

theorem add_tsub_le_assoc : a + b - c ≤ a + (b - c) := by
  grw [tsub_le_iff_left, add_left_comm, ← le_add_tsub]

