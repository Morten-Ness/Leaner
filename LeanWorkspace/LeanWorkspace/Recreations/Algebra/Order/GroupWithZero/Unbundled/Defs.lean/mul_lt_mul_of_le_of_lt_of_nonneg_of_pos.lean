import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_lt_mul_of_le_of_lt_of_nonneg_of_pos [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a ≤ b) (h₂ : c < d) (c0 : 0 ≤ c) (b0 : 0 < b) : a * c < b * d := (mul_le_mul_of_nonneg_right h₁ c0).trans_lt (mul_lt_mul_of_pos_left h₂ b0)

alias mul_lt_mul_of_nonneg_of_pos' := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos

