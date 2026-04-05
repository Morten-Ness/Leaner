import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_le_iff_left : a - b ≤ c ↔ a ≤ b + c := by rw [tsub_le_iff_right, add_comm]

