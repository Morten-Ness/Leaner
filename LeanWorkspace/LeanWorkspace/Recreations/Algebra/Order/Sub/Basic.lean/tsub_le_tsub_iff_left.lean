import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

variable [AddLeftReflectLE α]

theorem tsub_le_tsub_iff_left (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b := Contravariant.AddLECancellable.tsub_le_tsub_iff_left Contravariant.AddLECancellable h

