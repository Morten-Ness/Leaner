import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

theorem tsub_lt_of_lt (h : a < b) : a - c < b := lt_of_le_of_lt tsub_le_self h

