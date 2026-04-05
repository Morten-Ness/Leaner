import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_tsub (b a c : α) : b - a - c = b - (a + c) := by
  apply le_antisymm
  · rw [tsub_le_iff_left, tsub_le_iff_left, ← add_assoc, ← tsub_le_iff_left]
  · rw [tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left]

