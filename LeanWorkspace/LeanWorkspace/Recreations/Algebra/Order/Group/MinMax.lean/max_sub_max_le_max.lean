import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

theorem max_sub_max_le_max (a b c d : α) : max a b - max c d ≤ max (a - c) (b - d) := by
  grind

