import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α]

theorem tsub_le_tsub_left (h : a ≤ b) (c : α) : c - b ≤ c - a := tsub_le_iff_left.mpr <| le_add_tsub.trans <| by gcongr

