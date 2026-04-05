import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_tsub_le : b - (b - a) ≤ a := tsub_le_iff_right.mpr le_add_tsub

