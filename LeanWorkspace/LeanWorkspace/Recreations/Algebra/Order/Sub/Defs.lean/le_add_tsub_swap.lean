import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem le_add_tsub_swap : a ≤ b + a - b := Contravariant.AddLECancellable.le_add_tsub_swap

