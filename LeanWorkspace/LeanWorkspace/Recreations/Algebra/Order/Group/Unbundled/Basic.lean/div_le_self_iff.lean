import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] {a b c d : α}

theorem div_le_self_iff (a : α) {b : α} : a / b ≤ a ↔ 1 ≤ b := by
  simp [div_eq_mul_inv]

