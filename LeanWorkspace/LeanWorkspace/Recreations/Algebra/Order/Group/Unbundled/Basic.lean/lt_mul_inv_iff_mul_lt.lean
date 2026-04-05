import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulRightStrictMono α] {a b c : α}

theorem lt_mul_inv_iff_mul_lt : c < a * b⁻¹ ↔ c * b < a := (mul_lt_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel_right]

