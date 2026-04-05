import Mathlib

variable {α : Type*}

variable [Preorder α] [Add α] [Sub α] [OrderedSub α] {a b : α}

theorem add_tsub_le_right : a + b - b ≤ a := tsub_le_iff_right.mpr le_rfl

