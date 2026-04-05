import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem tsub_lt_tsub_left_of_le : b ≤ a → c < b → a - b < a - c := Contravariant.AddLECancellable.tsub_lt_tsub_left_of_le

