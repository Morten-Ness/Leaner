import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

theorem add_tsub_cancel_of_le (h : a ≤ b) : a + (b - a) = b := by
  refine le_antisymm ?_ le_add_tsub
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  grw [add_tsub_le_left]

