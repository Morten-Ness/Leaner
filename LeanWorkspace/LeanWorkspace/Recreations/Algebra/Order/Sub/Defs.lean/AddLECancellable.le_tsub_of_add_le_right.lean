import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem le_tsub_of_add_le_right (hb : AddLECancellable b) (h : a + b ≤ c) : a ≤ c - b := AddLECancellable.le_tsub_of_add_le_left hb <| by rwa [add_comm]

