import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulOneClass α] [Zero α] {a b c d : α}

variable [Preorder α]

theorem mul_le_iff_le_one_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b ≤ a ↔ b ≤ 1 := Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

