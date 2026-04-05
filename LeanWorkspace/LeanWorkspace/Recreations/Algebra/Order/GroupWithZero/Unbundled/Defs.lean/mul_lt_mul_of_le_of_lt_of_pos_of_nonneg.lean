import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_lt_mul_of_le_of_lt_of_pos_of_nonneg [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a ≤ b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 ≤ d) : a * c < b * d := (mul_lt_mul_of_pos_left h₂ a0).trans_le (mul_le_mul_of_nonneg_right h₁ d0)

alias mul_lt_mul_of_pos_of_nonneg := mul_lt_mul_of_le_of_lt_of_pos_of_nonneg

