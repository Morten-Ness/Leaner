import Mathlib

variable {α : Type u}

variable [Group α] [LE α]

variable [MulRightMono α] {a b c : α}

theorem div_le_div_right' (h : a ≤ b) (c : α) : a / c ≤ b / c := (div_le_div_iff_right c).2 h

