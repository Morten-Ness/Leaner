import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem add_add_tsub_cancel (hcb : c ≤ b) : a + c + (b - c) = a + b := Contravariant.AddLECancellable.add_add_tsub_cancel hcb

