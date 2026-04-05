import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LE α] [MulLeftMono α] {a b c d : α}

theorem div_le_iff_le_mul' : a / b ≤ c ↔ a ≤ b * c := by rw [div_le_iff_le_mul, mul_comm]

alias ⟨le_add_of_sub_left_le, sub_left_le_of_le_add⟩ := sub_le_iff_le_add'

