import Mathlib

variable {α : Type*}

variable {a b c : α} [LinearOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α]

theorem lt_of_tsub_lt_tsub_right (h : a - c < b - c) : a < b := lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_right h c) h

