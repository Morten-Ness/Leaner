import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem add_tsub_le_left : a + b - a ≤ b := tsub_le_iff_left.mpr le_rfl

