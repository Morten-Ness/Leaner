import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] {a b c : α}

theorem inv_mul_le_one_iff : a⁻¹ * b ≤ 1 ↔ b ≤ a := inv_mul_le_iff_le_mul.trans <| by rw [mul_one]

