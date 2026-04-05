import Mathlib

variable {α : Type*}

variable [Preorder α] [Add α] [Sub α] [OrderedSub α] {a b : α}

theorem le_tsub_add : b ≤ b - a + a := tsub_le_iff_right.mp le_rfl

