import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

theorem lt_div_iff_mul_lt' : b < c / a ↔ a * b < c := by rw [lt_div_iff_mul_lt, mul_comm]

alias ⟨add_lt_of_lt_sub_left, lt_sub_left_of_add_lt⟩ := lt_sub_iff_add_lt'

