import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

theorem tsub_pos_of_lt (h : a < b) : 0 < b - a := tsub_pos_iff_not_le.mpr h.not_ge

