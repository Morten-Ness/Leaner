import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] {a b c : α}

theorem le_inv_iff_mul_le_one_left : a ≤ b⁻¹ ↔ b * a ≤ 1 := (mul_le_mul_iff_left b).symm.trans <| by rw [mul_inv_cancel]

