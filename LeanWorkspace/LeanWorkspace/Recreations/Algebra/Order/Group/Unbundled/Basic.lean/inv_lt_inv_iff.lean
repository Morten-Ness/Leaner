import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

variable [MulRightStrictMono α]

theorem inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a := by
  rw [← mul_lt_mul_iff_left a, ← mul_lt_mul_iff_right b]
  simp

