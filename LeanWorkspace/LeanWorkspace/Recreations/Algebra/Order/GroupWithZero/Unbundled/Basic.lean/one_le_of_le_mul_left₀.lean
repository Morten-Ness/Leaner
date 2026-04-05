import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulOneClass α] [Zero α] {a b c d : α}

variable [Preorder α]

theorem one_le_of_le_mul_left₀ [PosMulReflectLE α] (ha : 0 < a) (h : a ≤ a * b) : 1 ≤ b := le_of_mul_le_mul_left (by simpa) ha

