import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem le_tsub_of_add_le_left (ha : AddLECancellable a) (h : a + b ≤ c) : b ≤ c - a := ha <| h.trans AddLECancellable.le_add_tsub

