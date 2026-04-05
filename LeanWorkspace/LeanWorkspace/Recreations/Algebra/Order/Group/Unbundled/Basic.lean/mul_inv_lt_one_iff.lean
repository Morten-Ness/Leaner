import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulRightStrictMono α] {a b c : α}

theorem mul_inv_lt_one_iff : b * a⁻¹ < 1 ↔ b < a := _root_.trans mul_inv_lt_iff_lt_mul <| by rw [one_mul]

