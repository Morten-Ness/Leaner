import Mathlib

variable {α : Type*}

variable {a b c : α} [LinearOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α]

theorem lt_tsub_comm : a < b - c ↔ c < b - a := lt_tsub_iff_left.trans lt_tsub_iff_right.symm

