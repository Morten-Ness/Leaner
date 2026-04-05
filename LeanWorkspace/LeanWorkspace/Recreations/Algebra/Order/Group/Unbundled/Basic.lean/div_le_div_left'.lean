import Mathlib

variable {α : Type u}

variable [Group α] [LE α]

variable [MulLeftMono α] [MulRightMono α] {a b c : α}

theorem div_le_div_left' (h : a ≤ b) (c : α) : c / b ≤ c / a := (div_le_div_iff_left c).2 h

