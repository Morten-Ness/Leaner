import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulRightMono α] {a b c : α}

theorem le_inv_iff_mul_le_one_right : a ≤ b⁻¹ ↔ a * b ≤ 1 := (mul_le_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel]

