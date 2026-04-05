import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [Preorder α]

theorem pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b := lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha

