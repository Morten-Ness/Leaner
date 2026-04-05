import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α]

theorem add_tsub_le_tsub_add : a + b - c ≤ a - c + b := by
  rw [add_comm, add_comm _ b]
  exact add_tsub_le_assoc

