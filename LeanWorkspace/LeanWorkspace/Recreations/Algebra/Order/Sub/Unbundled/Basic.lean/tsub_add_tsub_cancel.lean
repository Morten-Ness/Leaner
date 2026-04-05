import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_add_tsub_cancel (hab : b ≤ a) (hcb : c ≤ b) : a - b + (b - c) = a - c := by
  convert tsub_add_cancel_of_le (tsub_le_tsub_right hab c) using 2
  rw [tsub_tsub, add_tsub_cancel_of_le hcb]

