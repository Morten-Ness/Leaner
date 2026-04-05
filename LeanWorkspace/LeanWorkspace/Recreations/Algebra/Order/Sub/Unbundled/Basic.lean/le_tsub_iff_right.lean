import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem le_tsub_iff_right (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c := Contravariant.AddLECancellable.le_tsub_iff_right h

