import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [Preorder α]

theorem Right.mul_lt_mul_of_nonneg [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d := mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h₁ h₂.le a0 (c0.trans_lt h₂)

alias mul_lt_mul_of_nonneg := Left.mul_lt_mul_of_nonneg

alias mul_lt_mul'' := Left.mul_lt_mul_of_nonneg
attribute [gcongr] mul_lt_mul''

