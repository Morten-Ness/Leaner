import Mathlib

variable {α : Type u}

variable [Group α] [LE α]

variable [MulRightMono α] {a b c : α}

theorem le_div_iff_mul_le : a ≤ c / b ↔ a * b ≤ c := by
  rw [← mul_le_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨add_le_of_le_sub_right, le_sub_right_of_add_le⟩ := le_sub_iff_add_le

