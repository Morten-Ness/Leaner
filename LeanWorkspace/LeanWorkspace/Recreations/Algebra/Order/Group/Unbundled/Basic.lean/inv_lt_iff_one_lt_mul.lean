import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulRightStrictMono α] {a b c : α}

theorem inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a := (mul_lt_mul_iff_right a).symm.trans <| by rw [inv_mul_cancel]

