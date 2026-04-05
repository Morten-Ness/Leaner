import Mathlib

variable {α : Type u}

variable [Group α] [LT α]

variable [MulRightStrictMono α] {a b c : α}

theorem lt_div_iff_mul_lt : a < c / b ↔ a * b < c := by
  rw [← mul_lt_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨add_lt_of_lt_sub_right, lt_sub_right_of_add_lt⟩ := lt_sub_iff_add_lt

