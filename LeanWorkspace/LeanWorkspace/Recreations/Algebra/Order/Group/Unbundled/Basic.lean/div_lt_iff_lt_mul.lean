import Mathlib

variable {α : Type u}

variable [Group α] [LT α]

variable [MulRightStrictMono α] {a b c : α}

theorem div_lt_iff_lt_mul : a / c < b ↔ a < b * c := by
  rw [← mul_lt_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨lt_add_of_sub_right_lt, sub_right_lt_of_lt_add⟩ := sub_lt_iff_lt_add

