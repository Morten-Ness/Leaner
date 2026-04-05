import Mathlib

variable {α : Type u}

variable [Group α] [LT α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]
  {a b c : α}

theorem div_lt_div_left' (h : a < b) (c : α) : c / b < c / a := (div_lt_div_iff_left c).2 h

