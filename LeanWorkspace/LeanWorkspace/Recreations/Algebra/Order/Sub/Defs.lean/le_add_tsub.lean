import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem le_add_tsub : a ≤ b + (a - b) := tsub_le_iff_left.mp le_rfl

