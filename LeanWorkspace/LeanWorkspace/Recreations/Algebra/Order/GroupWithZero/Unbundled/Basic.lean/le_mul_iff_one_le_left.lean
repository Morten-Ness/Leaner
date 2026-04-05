import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulOneClass α] [Zero α] {a b c d : α}

variable [Preorder α]

theorem le_mul_iff_one_le_left [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : a ≤ b * a ↔ 1 ≤ b := Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ a0)

