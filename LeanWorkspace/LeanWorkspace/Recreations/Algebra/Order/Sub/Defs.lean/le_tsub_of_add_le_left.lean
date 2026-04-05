import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem le_tsub_of_add_le_left (h : a + b ≤ c) : b ≤ c - a := Contravariant.AddLECancellable.le_tsub_of_add_le_left h

