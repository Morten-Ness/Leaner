import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

theorem zero_tsub (a : α) : 0 - a = 0 := tsub_eq_zero_of_le <| zero_le a

