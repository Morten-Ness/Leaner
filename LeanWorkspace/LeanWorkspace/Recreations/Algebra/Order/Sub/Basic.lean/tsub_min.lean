import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

theorem tsub_min : a - min a b = a - b := (tsub_eq_tsub_min a b).symm

