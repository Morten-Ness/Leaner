import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] {a b c : α}

theorem inv_le_iff_one_le_mul' : a⁻¹ ≤ b ↔ 1 ≤ a * b := (mul_le_mul_iff_left a).symm.trans <| by rw [mul_inv_cancel]

