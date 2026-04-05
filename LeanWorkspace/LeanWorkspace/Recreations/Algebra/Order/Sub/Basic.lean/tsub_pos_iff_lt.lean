import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

theorem tsub_pos_iff_lt : 0 < a - b ↔ b < a := by rw [tsub_pos_iff_not_le, not_le]

