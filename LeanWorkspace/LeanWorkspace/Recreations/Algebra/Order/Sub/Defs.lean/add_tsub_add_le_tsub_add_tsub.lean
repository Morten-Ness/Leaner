import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α]

theorem add_tsub_add_le_tsub_add_tsub : a + b - (c + d) ≤ a - c + (b - d) := by
  rw [add_comm c, tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left]
  refine (tsub_le_tsub_right add_tsub_le_assoc c).trans ?_
  rw [add_comm a, add_comm (a - c)]
  exact add_tsub_le_assoc

