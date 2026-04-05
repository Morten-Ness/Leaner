import Mathlib

variable {α : Type u}

variable [Group α] [LE α]

variable [MulRightMono α] {a b c : α}

theorem one_le_div' : 1 ≤ a / b ↔ b ≤ a := by
  rw [← mul_le_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨le_of_sub_nonneg, sub_nonneg_of_le⟩ := sub_nonneg

