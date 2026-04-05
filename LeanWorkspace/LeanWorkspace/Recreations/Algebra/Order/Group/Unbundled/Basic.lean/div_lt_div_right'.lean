import Mathlib

variable {α : Type u}

variable [Group α] [LT α]

variable [MulRightStrictMono α] {a b c : α}

theorem div_lt_div_right' (h : a < b) (c : α) : a / c < b / c := (div_lt_div_iff_right c).2 h

