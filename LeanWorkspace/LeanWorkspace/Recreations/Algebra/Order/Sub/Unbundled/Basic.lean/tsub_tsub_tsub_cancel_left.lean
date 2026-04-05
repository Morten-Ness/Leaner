import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem tsub_tsub_tsub_cancel_left (h : b ≤ a) : a - c - (a - b) = b - c := Contravariant.AddLECancellable.tsub_tsub_tsub_cancel_left h

-- note: not generalized to `AddLECancellable` because `add_tsub_add_eq_tsub_left` isn't

