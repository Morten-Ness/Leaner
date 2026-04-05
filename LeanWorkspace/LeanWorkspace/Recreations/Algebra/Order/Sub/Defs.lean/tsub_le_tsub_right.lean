import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_le_tsub_right (h : a ≤ b) (c : α) : a - c ≤ b - c := tsub_le_iff_left.mpr <| h.trans le_add_tsub

