import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] {a b c d : α}

theorem le_div_self_iff (a : α) {b : α} : a ≤ a / b ↔ b ≤ 1 := by
  simp [div_eq_mul_inv]

alias ⟨_, sub_le_self⟩ := sub_le_self_iff

