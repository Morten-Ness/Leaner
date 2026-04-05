import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulLeftStrictMono α] {a b c : α}

theorem inv_lt_iff_one_lt_mul' : a⁻¹ < b ↔ 1 < a * b := (mul_lt_mul_iff_left a).symm.trans <| by rw [mul_inv_cancel]

