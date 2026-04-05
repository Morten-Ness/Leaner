import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

theorem div_lt_self_iff (a : α) {b : α} : a / b < a ↔ 1 < b := by
  simp [div_eq_mul_inv]

alias ⟨_, sub_lt_self⟩ := sub_lt_self_iff

