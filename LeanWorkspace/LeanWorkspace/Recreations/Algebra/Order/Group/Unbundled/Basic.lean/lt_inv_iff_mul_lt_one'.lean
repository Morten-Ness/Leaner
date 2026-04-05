import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulLeftStrictMono α] {a b c : α}

theorem lt_inv_iff_mul_lt_one' : a < b⁻¹ ↔ b * a < 1 := (mul_lt_mul_iff_left b).symm.trans <| by rw [mul_inv_cancel]

