import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α]

theorem le_tsub_add_add : a + b ≤ a - c + (b + c) := by
  rw [add_comm a, add_comm (a - c)]
  exact add_le_add_add_tsub

