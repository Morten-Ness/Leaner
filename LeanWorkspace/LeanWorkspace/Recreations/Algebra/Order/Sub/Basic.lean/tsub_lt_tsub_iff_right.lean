import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

variable [AddLeftReflectLE α]

theorem tsub_lt_tsub_iff_right (h : c ≤ a) : a - c < b - c ↔ a < b := Contravariant.AddLECancellable.tsub_lt_tsub_iff_right h

