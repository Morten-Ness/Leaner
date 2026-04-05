import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulOneClass α] [Zero α] {a b c d : α}

variable [Preorder α]

theorem one_le_of_le_mul_right₀ [MulPosReflectLE α] (hb : 0 < b) (h : b ≤ a * b) : 1 ≤ a := le_of_mul_le_mul_right (by simpa) hb

