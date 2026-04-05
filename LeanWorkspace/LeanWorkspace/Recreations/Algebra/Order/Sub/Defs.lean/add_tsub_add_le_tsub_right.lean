import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α]

theorem add_tsub_add_le_tsub_right : a + c - (b + c) ≤ a - b := by
  grw [tsub_le_iff_left, add_right_comm, ← le_add_tsub]

