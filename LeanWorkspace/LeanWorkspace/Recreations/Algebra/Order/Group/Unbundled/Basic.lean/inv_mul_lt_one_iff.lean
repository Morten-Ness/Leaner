import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulLeftStrictMono α] {a b c : α}

theorem inv_mul_lt_one_iff : a⁻¹ * b < 1 ↔ b < a := _root_.trans inv_mul_lt_iff_lt_mul <| by rw [mul_one]

