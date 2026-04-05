import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

variable [AddLeftReflectLE α]

theorem tsub_lt_tsub_iff_left_of_le (h : b ≤ a) : a - b < a - c ↔ c < b := Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le Contravariant.AddLECancellable h

