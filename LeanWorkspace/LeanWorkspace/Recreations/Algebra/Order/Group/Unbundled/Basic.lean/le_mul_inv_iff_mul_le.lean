import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulRightMono α] {a b c : α}

theorem le_mul_inv_iff_mul_le : c ≤ a * b⁻¹ ↔ c * b ≤ a := (mul_le_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel_right]

