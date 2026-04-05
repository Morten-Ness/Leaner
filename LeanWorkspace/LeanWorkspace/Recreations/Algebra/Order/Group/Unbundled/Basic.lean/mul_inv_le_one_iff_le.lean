import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulRightMono α] {a b c : α}

theorem mul_inv_le_one_iff_le : a * b⁻¹ ≤ 1 ↔ a ≤ b := mul_inv_le_iff_le_mul.trans <| by rw [one_mul]

