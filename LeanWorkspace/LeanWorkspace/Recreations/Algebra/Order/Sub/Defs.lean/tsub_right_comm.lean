import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_right_comm : a - b - c = a - c - b := by
  rw [← tsub_add_eq_tsub_tsub, tsub_add_eq_tsub_tsub_swap]

