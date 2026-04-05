import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [Preorder α]

theorem Left.mul_lt_mul_of_nonneg [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos h₁.le h₂ c0 (a0.trans_lt h₁)

