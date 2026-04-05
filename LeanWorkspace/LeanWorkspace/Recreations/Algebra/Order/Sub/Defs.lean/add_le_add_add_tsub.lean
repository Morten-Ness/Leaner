import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α]

theorem add_le_add_add_tsub : a + b ≤ a + c + (b - c) := by grw [add_assoc, ← le_add_tsub]

