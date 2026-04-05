import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LE α] [MulLeftMono α] {a b c d : α}

theorem le_div_iff_mul_le' : b ≤ c / a ↔ a * b ≤ c := by rw [le_div_iff_mul_le, mul_comm]

alias ⟨add_le_of_le_sub_left, le_sub_left_of_add_le⟩ := le_sub_iff_add_le'

