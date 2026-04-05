import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulRightMono α] {a b c : α}

theorem mul_inv_le_iff_le_mul : a * b⁻¹ ≤ c ↔ a ≤ c * b := (mul_le_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel_right]

