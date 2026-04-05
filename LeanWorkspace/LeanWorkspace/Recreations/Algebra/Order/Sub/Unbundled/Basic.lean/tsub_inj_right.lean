import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem tsub_inj_right (h₁ : b ≤ a) (h₂ : c ≤ a) (h₃ : a - b = a - c) : b = c := Contravariant.AddLECancellable.tsub_inj_right h₁ h₂ h₃

