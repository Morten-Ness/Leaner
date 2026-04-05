import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_lt_mul_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (c0 : 0 < c) (b0 : 0 < b) : a * c < b * d := (mul_lt_mul_of_pos_right h₁ c0).trans (mul_lt_mul_of_pos_left h₂ b0)

alias mul_le_mul := mul_le_mul_of_nonneg'
attribute [gcongr] mul_le_mul

alias mul_lt_mul := mul_lt_mul_of_pos_of_nonneg'

alias mul_lt_mul' := mul_lt_mul_of_nonneg_of_pos'

