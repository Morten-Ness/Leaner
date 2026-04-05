import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

variable [MulRightStrictMono α]

theorem inv_lt' : a⁻¹ < b ↔ b⁻¹ < a := by rw [← inv_lt_inv_iff, inv_inv]

