import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

theorem lt_of_tsub_lt_tsub_right_of_le (h : c ≤ b) (h2 : a - c < b - c) : a < b := by
  refine ((tsub_le_tsub_iff_right h).mp h2.le).lt_of_ne ?_
  rintro rfl
  exact h2.false

