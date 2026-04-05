import Mathlib

variable {α : Type u}

variable [Group α] [LT α]

variable [MulRightStrictMono α] {a b c : α}

theorem one_lt_div' : 1 < a / b ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨lt_of_sub_pos, sub_pos_of_lt⟩ := sub_pos

