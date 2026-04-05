import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

theorem tsub_le_self : a - b ≤ a := tsub_le_iff_left.mpr <| le_add_left le_rfl

