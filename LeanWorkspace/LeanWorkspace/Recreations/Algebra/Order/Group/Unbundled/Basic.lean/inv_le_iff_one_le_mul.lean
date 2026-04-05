import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulRightMono α] {a b c : α}

theorem inv_le_iff_one_le_mul : a⁻¹ ≤ b ↔ 1 ≤ b * a := (mul_le_mul_iff_right a).symm.trans <| by rw [inv_mul_cancel]

