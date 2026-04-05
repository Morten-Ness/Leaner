import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [Preorder α]

theorem pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a := lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb

