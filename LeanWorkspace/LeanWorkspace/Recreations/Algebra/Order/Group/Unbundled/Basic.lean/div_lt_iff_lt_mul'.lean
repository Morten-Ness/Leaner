import Mathlib

variable {α : Type u}

variable [CommGroup α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

theorem div_lt_iff_lt_mul' : a / b < c ↔ a < b * c := by rw [div_lt_iff_lt_mul, mul_comm]

alias ⟨lt_add_of_sub_left_lt, sub_left_lt_of_lt_add⟩ := sub_lt_iff_lt_add'

