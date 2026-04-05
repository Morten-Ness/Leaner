import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulRightMono α] {a b c : α}

theorem mul_inv_le_one_iff : b * a⁻¹ ≤ 1 ↔ b ≤ a := _root_.trans mul_inv_le_iff_le_mul <| by rw [one_mul]

