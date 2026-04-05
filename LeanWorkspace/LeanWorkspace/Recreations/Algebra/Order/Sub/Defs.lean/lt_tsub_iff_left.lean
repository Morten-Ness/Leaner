import Mathlib

variable {α : Type*}

variable {a b c : α} [LinearOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α]

theorem lt_tsub_iff_left : a < b - c ↔ c + a < b := lt_iff_lt_of_le_iff_le tsub_le_iff_left

