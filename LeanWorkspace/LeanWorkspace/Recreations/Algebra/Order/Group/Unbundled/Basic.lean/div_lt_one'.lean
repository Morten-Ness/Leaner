import Mathlib

variable {α : Type u}

variable [Group α] [LT α]

variable [MulRightStrictMono α] {a b c : α}

theorem div_lt_one' : a / b < 1 ↔ a < b := by
  rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨lt_of_sub_neg, sub_neg_of_lt⟩ := sub_neg

alias sub_lt_zero := sub_neg

