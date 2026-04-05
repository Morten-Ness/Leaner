import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

theorem tsub_self_add (a b : α) : a - (a + b) = 0 := tsub_eq_zero_of_le <| self_le_add_right _ _

