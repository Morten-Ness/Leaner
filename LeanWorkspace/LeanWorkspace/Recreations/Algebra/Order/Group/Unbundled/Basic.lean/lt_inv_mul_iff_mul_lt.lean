import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulLeftStrictMono α] {a b c : α}

theorem lt_inv_mul_iff_mul_lt : b < a⁻¹ * c ↔ a * b < c := by
  rw [← mul_lt_mul_iff_left a]
  simp

