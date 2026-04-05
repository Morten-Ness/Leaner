import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulOneClass α] [Zero α] {a b c d : α}

variable [Preorder α]

theorem mul_le_iff_le_one_left [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b) : a * b ≤ b ↔ a ≤ 1 := Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ b0)

