import Mathlib

variable {α : Type u}

variable [Group α] [LE α]

variable [MulRightMono α] {a b c : α}

theorem div_le_one' : a / b ≤ 1 ↔ a ≤ b := by
  rw [← mul_le_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨le_of_sub_nonpos, sub_nonpos_of_le⟩ := sub_nonpos

